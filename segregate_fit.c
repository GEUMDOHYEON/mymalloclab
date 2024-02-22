// 분리 맞춤 Segregate-fits
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "team 4",
    "DOHYEON GEUM",
    "dohyeon0518@gmail.com",
    "",
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본 상수 & 매크로 */
#define WSIZE 4              // word size
#define DSIZE 8              // double word size
#define CHUNKSIZE (1 << 12)  // 힙 확장을 위한 기본 크기 (= 초기 빈 블록의 크기)
#define SEGREGATED_SIZE (12) // segregated list의 class 개수
#define MAX(x, y) (x > y ? x : y)

/* 가용 리스트를 접근/순회하는 데 사용할 매크로 */
#define PACK(size, alloc) (size | alloc)                             
#define GET(p) (*(unsigned int *)(p))                               
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))    
#define GET_SIZE(p) (GET(p) & ~0x7)                               
#define GET_ALLOC(p) (GET(p) & 0x1)                                 
#define HDRP(bp) ((char *)(bp)-WSIZE)                                 
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)         
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) 
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   

static char *heap_listp;                                // 클래스의 시작
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))



static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void remove_free(void *bp); // 가용 리스트에서 제거
static void add_free(void *bp);    // 가용 리스트에 추가
static int get_class(size_t size);


int mm_init(void)
{
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성
        return -1;
    PUT(heap_listp, 0);                                                   
    PUT(heap_listp + (1 * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Header (크기: 헤더 1 + 풋터 1 + segregated list 크기)
    for (int i = 0; i < SEGREGATED_SIZE; i++)
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); //프롤로그 풋터
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));                            
    heap_listp += (2 * WSIZE);
    if (extend_heap(4) == NULL)
        return -1;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;

    // 더블 워드 정렬 유지
    // size: 확장할 크기
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 2워드의 가장 가까운 배수로 반올림 (홀수면 1 더해서 곱함)

    if ((long)(bp = mem_sbrk(size)) == -1) // 힙 확장
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새 빈 블록 헤더 초기화
    PUT(FTRP(bp), PACK(size, 0));         // 새 빈 블록 푸터 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 블록 헤더 초기화

    return coalesce(bp); // 병합 후 리턴 블록 포인터 반환
}

static void place(void *bp, size_t asize){
    remove_free(bp); // free_list에서 해당 블록 제거

    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동

        PUT(HDRP(bp), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(bp), PACK((csize - asize), 0));
        add_free(bp); // 남은 블록을 free_list에 추가
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * brk 포인터를 증가시켜 블록을 할당
 *     alignment(DSIZE = 8)의 배수의 크기인 블록을 할당
 */
void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 사이즈
    size_t extendsize; // 확장할 사이즈
    char *bp;

    if (size == 0) // 잘못된 요청 분기
        return NULL;

    if (size <= DSIZE)     // 8바이트 이하이면
        asize = 2 * DSIZE; // 최소 블록 크기 16바이트 할당 (헤더 4 + 푸터 4 + 저장공간 8)
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); // 8배수로 올림 처리

    if ((bp = find_fit(asize)) != NULL) // 가용 블록 검색
    {
        place(bp, asize); // 할당
        return bp;        // 새로 할당된 블록의 포인터 리턴
    }

    // 적합한 블록이 없을 경우 힙확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}
static void remove_free(void* bp){
    int class = get_class(GET_SIZE(HDRP(bp)));
    if(bp == GET_ROOT(class)){
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class));
        return;
    }
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);

    if(GET_SUCC(bp) != NULL){
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
    }
    
}
static void add_free(void* bp){
    int class = get_class(GET_SIZE(HDRP(bp)));
    GET_SUCC(bp) = GET_ROOT(class);
    if(GET_ROOT(class) != NULL){
        GET_PRED(GET_ROOT(class)) = bp;
    }
    GET_ROOT(class) = bp;
}
/*
 * coalesce - 가용 블록들을 병합 시켜주는 함수.
 * 병합하는 경우에 주변 블록들의 경우의 수는 네가지가 존재한다.
 *          이 전 | 현 재 | 다 음
 * case 1:   X      O      X
 * case 2:   X      O      O
 * case 3:   O      O      X
 * case 4:   O      O      O
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

    if (prev_alloc && next_alloc) // 모두 할당된 경우
    {
        add_free(bp); // free_list에 추가
        return bp;          // 블록의 포인터 반환
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        remove_free(NEXT_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        remove_free(PREV_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    else // 이전 블록과 다음 블록 모두 빈 경우
    {
        remove_free(PREV_BLKP(bp)); // 이전 가용 블록을 free_list에서 제거
        remove_free(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    add_free(bp); // 현재 병합한 가용 블록을 free_list에 추가
    return bp;          // 병합한 가용 블록의 포인터 반환
}

void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
        return mm_malloc(size);
    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

    void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
        return NULL; // 할당 실패

    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload만큼 복사
    if (size < copySize)                           // 기존 사이즈가 새 크기보다 더 크면
        copySize = size;                           // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사
    mm_free(ptr);                  // 기존 블록 해제
    return newptr;
}
int mm_check(void){
    return 1;
}

static void *find_fit(size_t asize){
    int class = get_class(asize);
    void *bp = GET_ROOT(class);
    while(class < SEGREGATED_SIZE){
        bp = GET_ROOT(class);
        while(bp != NULL){
            if((asize <= GET_SIZE(HDRP(bp)))){
                return bp;
            }
            bp = GET_SUCC(bp);
        }
        class += 1;
    }
    return NULL;
}

int get_class(size_t size){
    if (size < 16) // 최소 블록 크기는 16바이트
        return -1; // 잘못된 크기

    // 클래스별 최소 크기
    size_t class_sizes[SEGREGATED_SIZE];
    class_sizes[0] = 16;

    // 주어진 크기에 적합한 클래스 검색
    for (int i = 0; i < SEGREGATED_SIZE; i++)
    {
        if (i != 0)
            class_sizes[i] = class_sizes[i - 1] << 1;
        if (size <= class_sizes[i])
            return i;
    }

    // 주어진 크기가 8192바이트 이상인 경우, 마지막 클래스로 처리
    return SEGREGATED_SIZE - 1;
}


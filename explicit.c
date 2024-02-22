/////////////////////////////////////////  
//명시적 가용 리스트 //

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "team4",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* Basic constants and macros */
#define WSIZE 4 // Word and header/footer size (bytes)
#define DSIZE 8 // Double word size (bytes)
#define CHUNKSIZE (1<<8) // Extend heap by this amount - 힙을 이만큼 늘려라 (bytes) 

#define MAX(x,y) ((x>y)? x : y) // If x is greater than y, select x. Otherwise (if y is greater), select y. (max function defined - 맥스함수 정의)

#define MIN(x,y) ((x>y)? y : x) // If x is greater than y, select x. Otherwise (if y is greater), select y. (max function defined - 맥스함수 정의)
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size)|(alloc)) // 크기와 할당 비트 통합 - 헤더와 풋터에 저장할 수 있는 값 리턴 

/* Read and write a word at address p */
#define GET(p)          (*(unsigned int *)(p))        // get the address of 'p' - p가 참조하는 워드를 읽어서 리턴 
#define PUT(p, val)     (*(unsigned int *)(p)=(val))   // put 'val' into address 'p' - p가 가리키는 워드에 val을 저장

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char*)(bp) - WSIZE)
#define FTRP(bp)        ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char*)(bp) + GET_SIZE(((char*)(bp)) - WSIZE))
#define PREV_BLKP(bp)   ((char*)(bp) - GET_SIZE(((char*)(bp)) - DSIZE))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static char *free_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void splice_free_block(void *bp);
static void add_free_block(void *bp);

int mm_init(void)
{
    // 초기 힙 생성
    if ((free_listp = mem_sbrk(8 * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, free_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    PUT(free_listp, 0);                                // 정렬 패딩
    PUT(free_listp + (1 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Header
    PUT(free_listp + (2 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Footer
    PUT(free_listp + (3 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 헤더
    PUT(free_listp + (4 * WSIZE), NULL);               // 이전 가용 블록의 주소
    PUT(free_listp + (5 * WSIZE), NULL);               // 다음 가용 블록의 주소
    PUT(free_listp + (6 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 푸터
    PUT(free_listp + (7 * WSIZE), PACK(0, 1));         // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄

    free_listp += (4 * WSIZE); // 첫번째 가용 블록의 bp

    // 힙을 CHUNKSIZE bytes로 확장
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

    return coalesce(bp); // 병합 후 coalesce 함수에서 리턴된 블록 포인터 반환
}

static void splice_free_block(void *bp)
{
    if (bp == free_listp) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        free_listp = GET_SUCC(free_listp); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

static void add_free_block(void *bp)
{
    GET_SUCC(bp) = free_listp;     // bp의 SUCC은 루트가 가리키던 블록
    if (free_listp != NULL)        // free list에 블록이 존재했을 경우만
        GET_PRED(free_listp) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    free_listp = bp;               // 루트를 현재 블록으로 변경
}

static void place(void *bp, size_t asize)
{
    splice_free_block(bp); // free_list에서 해당 블록 제거

    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
        add_free_block(NEXT_BLKP(bp)); // 남은 블록을 free_list에 추가
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 사이즈
    size_t extendsize; // 확장할 사이즈
    char *bp;

    // 잘못된 요청 분기
    if (size == 0)
        return NULL;

		/* 사이즈 조정 */
    if (size <= DSIZE)     // 8바이트 이하이면
        asize = 2 * DSIZE; // 최소 블록 크기 16바이트 할당 (헤더 4 + 푸터 4 + 저장공간 8)
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); // 8배수로 올림 처리

		/* 가용 블록 검색 */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); // 할당
        return bp;        // 새로 할당된 블록의 포인터 리턴
    }

    /* 적합한 블록이 없을 경우 힙확장 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) // 메모리 반환해주는 코드(= 가용 블록으로 변환) -> 할당비트를 0으로 만들고 coalesce() 호출
{
    size_t size = GET_SIZE(HDRP(ptr)); // 크기는 변하지 않고 할당 비트만 바꿔주어야 하니 반환되는 블록의 크기를 가져옴

    PUT(HDRP(ptr), PACK(size, 0)); // 헤더에 할당 비트만 0으로 변환됨
    PUT(FTRP(ptr), PACK(size, 0)); // 풋터에 할당 비트만 0으로 변환됨
    coalesce(ptr); // 가용 블록으로 변환이 되어 이전 블록의 연결과 단편화를 막기 위해 coalesce() 호출
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
        add_free_block(bp); // free_list에 추가
        return bp;          // 블록의 포인터 반환
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        splice_free_block(NEXT_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    else // 이전 블록과 다음 블록 모두 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 이전 가용 블록을 free_list에서 제거
        splice_free_block(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    add_free_block(bp); // 현재 병합한 가용 블록을 free_list에 추가
    return bp;          // 병합한 가용 블록의 포인터 반환
}

void *mm_realloc(void *ptr, size_t size)
{
		/* 예외 처리 */
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
        return mm_malloc(size);

    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

		/* 새 블록에 할당 */
    void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
        return NULL; // 할당 실패

		/* 데이터 복사 */
    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload만큼 복사
    if (size < copySize)                           // 기존 사이즈가 새 크기보다 더 크면
        copySize = size;                           // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사

		/* 기존 블록 반환 */
    mm_free(ptr);

    return newptr;
}

int mm_check(void){
    return 1;
}

// static void *find_fit(size_t asize) // best fit
// {
//     void *bp;
//     void *best_fit = NULL;

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
//             // 기존에 할당하려던 공간보다 더 최적의 공간이 나타났을 경우 리턴 블록 포인터 갱신
//             if (!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit))) 
//                 best_fit = bp;
    
//     return best_fit;
// }

static void *find_fit(size_t asize) //first fit
{
    void *bp = free_listp;

    while (bp != NULL){
        if ((asize <= GET_SIZE(HDRP(bp)))) return bp;
        bp = GET_SUCC(bp);
    }
    return NULL;
}


static void *find_fit(size_t asize) 
{
    void *bp = NEXT_BLKP(heap_listp);
    void *best_fit = NULL;

    // 에필로그 헤더를 만날 때까지 반복
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp= NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize < GET_SIZE(HDRP(bp)))){
            if (!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit))){
                best_fit = bp;
            }
        }
    } return best_fit;
}


static void *find_fit(size_t asize) // best fit
{
    void *bp;
    void *best_fit = NULL;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            // 기존에 할당하려던 공간보다 더 최적의 공간이 나타났을 경우 리턴 블록 포인터 갱신
            if (!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit))) 
                best_fit = bp;
    
    return best_fit;
}

static void *find_fit(size_t asize) //first fit
{
    void *bp;

    // 에필로그 블록의 헤더를 0으로 넣어줬으므로 에필로그 블록을 만날 때까지 탐색을 진행한다.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    
    return NULL;
}


void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; // 이전 포인터
    void *newptr; // 새로 메모리 할당할포인터

    size_t originsize = GET_SIZE(HDRP(oldptr)); // 원본 사이즈
    size_t newsize = size + DSIZE; // 새 사이즈

    // size 가 더 작은 경우
    if (newsize <= originsize) { 
        return oldptr;
    } else {
        size_t addSize = originsize + GET_SIZE(HDRP(NEXT_BLKP(oldptr))); // 추가 사이즈 -> 헤더 포함 사이즈
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (newsize <= addSize)){ // 가용 블록이고 사이즈 충분
            PUT(HDRP(oldptr), PACK(addSize, 1)); // 새로운 헤더
            PUT(FTRP(oldptr), PACK(addSize, 1)); // 새로운 푸터
            return oldptr;
        } else {
            newptr = mm_malloc(newsize);
            if (newptr == NULL)
                return NULL;
            memmove(newptr, oldptr, newsize); // memcpy 사용 시, memcpy-param-overlap 발생
            mm_free(oldptr);
            return newptr;
        }
    }
}

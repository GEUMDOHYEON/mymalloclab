#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team4",
    /* First member's full name */
    "GEUM DOHYEON",
    /* First member's email address */
    "dohyeon0518@gmail.com",
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


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


static char *next_heap_listp;
static char *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    //creating the initial empty heap - 초기 빈 힙공간 만들기 
    /* 
     * mem_sbrk - simple model of the sbrk function. Extends the heap 
     * by incr bytes and returns the start address of the new area. In
     * this model, the heap cannot be shrunk.
     * sbrk 함수의 단수화된 형태. 힙을 incr바이트만큼 늘리고 이 새 공간의
     * 시작 주소를 반환한다. 이 형태의 sbrk함수로는 힙의 크기를 줄일 수 없다.   
     */
    
    //4워드의 크기로 heap 초기화
    heap_listp = mem_sbrk(4*WSIZE);
    if (heap_listp == (void*)-1) 
    // mem_sbrk가 -1을  반환했다면 incr를 음수로 넣었거나 메모리가 꽉 찼다는 말이다.
    // 축소하라는 명령은 거부하며, 메모리를 더 못 늘리는 상황에도 거부한다. 
        return -1;  
    // initialization
    PUT(heap_listp, 0); // unused padding word - 미사용 패딩 워드
    // 연결과정 동안에 가장자리 조건을 없애주기 위한 속임수 - prologue & epilogue
    PUT(heap_listp + (WSIZE), PACK(DSIZE,1));  // prologue block header (8/1) does not returned
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); // prologue block footer (8/1) does not get returned - blocks assigned via malloc come after this word 
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); // epilogue block header (0/1) size 0. 
    heap_listp += (2*WSIZE);
    next_heap_listp = heap_listp;

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1; //1024
    return 0;
}

static void *extend_heap(size_t words) // 힙을 늘려주는 함수 (아래 두 가지에 시행됨 1. 힙이 초기화될 때 2. mm_malloc() 호출 시 알맞은 메모리 크기가 없을 때)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : (words) * WSIZE; // 8바이트(더블  워드)씩 정렬 유지를 위한 코드
    if((long) (bp = mem_sbrk(size)) == -1){ // mem_sbrk 함수를 통해 힙 영역을 늘림(실제로 힙 영역을 늘리는 부분)
        return NULL; // mem_sbrk 실패 시 -1을 반환하기 때문에 예외 처리 코드
    }
    // 각 블록의 헤더와 풋터는 해당 블록의 크기와 할당 비트로 이루어져 있기 때문에 size와 할당 비트를 같이 할당해 주어야 한다. 할당 비트는 0으로 고정
    PUT(HDRP(bp), PACK(size,0)); // 블록의 헤더 값 할당 
    PUT(FTRP(bp), PACK(size,0)); // 블록의 풋터 값 할당
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // 힙 자체를 늘려주다 보니 묵시적 가용 리스트의 끝을 나타내는 에필로그 블록 할당이 필수적

    return coalesce(bp); // 단지 늘리기만 했으므로 이전 블록과 연결시켜야함. 또한 단편화를 막기 위해 coalesce 함수 호출이 필요
}


static void place(void *bp, size_t asize){
    size_t total_size = GET_SIZE(HDRP(bp));

    //만약 블록 크기가 요청받은 크기보다 클 시, 남은 부분을 0으로 설정하여 다시 가용 리스트로 반환
    if (total_size-asize >= 2*DSIZE) {
        //요청받은 크기 asize만큼 할당 (alloc)
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK((total_size - asize), 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK((total_size - asize), 0));
        next_heap_listp = NEXT_BLKP(bp);
    }
    else {
        PUT(HDRP(bp), PACK(total_size, 1));
        PUT(FTRP(bp), PACK(total_size, 1));
        next_heap_listp = NEXT_BLKP(bp);
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
    // 입력받는 size가 ALIGNMENT의 배수가 아닐 수 있기 때문에 크기가 조정되어야 한다. 
    // 
    size_t asize; 
    size_t extendsize; // amount to extend heap if no fit - 핏이 안되는 경우, heap을 늘릴 크기 
    char *bp; // 블록포인터

    //거짓 요청 무시
    if (size == 0) return NULL; // 요청받은 블록의 크기가 0이면 NULL을 반환 

    // 오버헤드와 정렬 조건을 맞추기 위해 블록 사이즈 조절
    // 최소 16바이트 크기의 블록을 구성한다 - 8바이트는 정렬 조건을 맞추기 위해, 나머지 8바이트는 헤더와 풋터 오버헤드를 위해. 
    if (size <= DSIZE) asize = 2*DSIZE; // 요청받은 블록의 크기가 DSIZE보다 작거나 같은 경우, asize에 2*DSIZE(16)을 넣는다 (헤더(4) + 더블워드(8) + 풋터(8) )
    // 주어진 size에 (DSIZE-1)을 더한 후 int division으로 /DSIZE 한 후 다시 DSIZE와 곱해주면 정렬 조건을 만족한다. 
    // 여기에 DSIZE가 한 번 더 더해지는 이유는, 오버헤드 조건을 맞추기 위해서이다. 
    // 예를 들어, 주어진 size가 13인 경우 아래 식을 수행하면 단계별로 아래와 같다.
    // 8 * ((13 + 8+ 7)/8)
    // 8 * ((28)/8) <- int division을 통해 소수점 아래 수는 없어진다 
    // 8 * 3 
    // 24 
    // 이 중 8 바이트는 오버헤드를 위한 것임으로, 8의 배수중 실제로 입력된 값(13)보다 크면서 가장 근접한 수인 16바이트로 조정된다.   
    // else asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/DSIZE); 
    else asize = ALIGN(size) + DSIZE;

    /* Search the free list for a fit */
    //find_fit과 place 아직 미구현 단계//
    /* 가용 리스트에서 asize가 들어갈 수 있는 블록을 탐색
        해당 블록의 블록포인터를 반환, NULL이 아닐 시 
        해당 위치의 asize 크기의 블록을 할당후 주소 반환 
        *** 이미 할당된 후 반환된 가용 블록 중 재할당 가능한 블록이 있을 시에만 할당 후 bp(주소) 반환, 리턴
    */
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        next_heap_listp = bp;
        return bp;
    }

    /*No fit found. Get more memoery and place the block*/
    /* 맞는 핏의 가용 블록이 없을 시, (힙을 늘려서)추가 메모리 확보 후 할당 */
    extendsize = MAX(asize, CHUNKSIZE); // asize 또는 CHUNKSIZE(1<<12) 중 더 높은 수를 늘려야( 하는 크기로 설정
    if((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL; // 늘릴 수 없는 상황이면 (incr가 음수로 들어갔거나), 메모리가 부족하면) NULL 반환
    //위와 비슷하다. 새로운 영역의 주소가 위 줄에서 bp에 넣어졌으며, 해당 위치에 asize크기의 블록을 할당한다.
    place(bp, asize);
    next_heap_listp = bp;
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
    // 이전 블록이 사용중인지 확인
    size_t prev_block_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp))); // 현재 블록 포인터 - DSIZE = 이전 블록의 풋터
    // 다음 블록이 사용중인지 확인
    size_t next_block_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 현재 블록의 사이즈 구하기
    size_t block_size = GET_SIZE(HDRP(bp));

    // case 1: 이전, 다음 블록 모두 사용중일 때
    if (prev_block_alloc && next_block_alloc) return bp;

    // case 2: 이전 블록은 사용중이고, 다음 블록이 비어있을 때 => 현재 블록과 다음 블록 병합
    else if (prev_block_alloc && !next_block_alloc) {
        block_size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 병합했을 때의 크기를 구한다
        PUT(HDRP(bp), PACK(block_size, 0)); // 현재 블록의 헤더에 병합한 블록 크기를 갱신해준다
        PUT(FTRP(bp), PACK(block_size, 0)); // 현재 블록의 풋터에 병합한 블록 크기를 갱신해준다
        // 블록 포인터는 이전과 동일하다
    }
    
    // case 3: 이전 블록이 비어있고, 다음 블록은 사용중일 때 => 이전 블록과 현재 블록 병합
    else if (!prev_block_alloc && next_block_alloc) {
        block_size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 병합했을 때의 크기를 구한다
        PUT(HDRP(PREV_BLKP(bp)), PACK(block_size, 0)); // 이전 블록의 헤더에 병합한 크기를 갱신해준다
        PUT(FTRP(bp), PACK(block_size, 0)); // 현재 블록의 풋터에 병합한 크기를 갱신해준다
        bp = PREV_BLKP(bp); // 병합한 블록을 가리키는 포인터로 갱신해준다
    }

    // case 4: 이전, 다음 블록 모두 비어져있을 때 => 이전 블록, 현재 블록, 다음 블록 병합
    else {
        block_size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 크기를 더한다
        block_size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 크기를 더한다
        PUT(HDRP(PREV_BLKP(bp)), PACK(block_size, 0)); // 이전 블록의 헤더에 병합한 블록 크기를 갱신해준다
        bp = PREV_BLKP(bp); // 이전 블록의 포인터로 이동한다
        PUT(FTRP(bp), PACK(block_size, 0)); // 이동된 포인터 기준으로의 풋터에 병합한 블록 크기를 갱신해준다
    }
    next_heap_listp = bp;
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// realloc의 매개변수 중 size가 0이면 free, ptr = null이고 사이즈 값만 받으면 malloc
// 재할당은 원하는 크기만큼 원래 블록 자체를 조절하는 것이 아니라 새로운 블록을 찾아서 원하는 크기 만큼의 블록을 새롭게 할당하는 것
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr; // 새로운 블록
    size_t copySize; // 이전 블록의 복사할 크기

    if (ptr == NULL){ // ptr이 NULL인 경우 -> ptr을 재할당을 해주어야 하는데 원래 블록이 없으니 새롭게 만들어준다.
        return mm_malloc(size); // malloc 시행
    }

    if (size == 0){ // size가 0인 경우 -> 해당 블록의 크기를 0으로 조절하는 것이다 보니 free와 동일한 동작을 수행한다.
        mm_free(ptr);
        return 0;
    }

    newptr = mm_malloc(size); // 원하는 크기만큼 새로운 블록을 만든다.
    if (newptr == NULL) 
        return NULL;

    copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // 이전에 할당된 메모리 블록의 크기 = payload 부분만 필요
    if (size < copySize) // 이전 블록의 크기가 큰 경우
        copySize = size; // 위의 경우라면 메모리 블록을 복사하면 메모리가 넘칠 수 있기 때문에 예외 처리를 해준다.
    memcpy(newptr, ptr, copySize); // 재할당은 크기를 조절하는 것이여서 새롭게 생기는 블록에 이전 블록의 데이터가 있어야 하기 때문애 데이터 복사가 필요하다.
    mm_free(ptr); // 원래 블록 할당 해제
    return newptr;
}


static void *find_fit(size_t asize) //next fit
{
    char *bp;
    if (next_heap_listp == NULL){
        next_heap_listp = heap_listp;
    }

    // next_fit 포인터에서 탐색을 시작한다.
    for (bp = NEXT_BLKP(next_heap_listp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    
    for (bp = heap_listp; bp <= next_heap_listp; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;

    return NULL;
}

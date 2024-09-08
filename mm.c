/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p가 가리키는 메모리 주소에 값 val을 저장

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 현재 블록 bp의 다음 블록의 시작 주소를 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;

static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *ptr, size_t size);
static void *coalesce(void *bp);
void mm_free(void *ptr);
void *mm_malloc(size_t size);
static void *extend_heap(size_t words);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding - 더블워드 경계로 정렬된 미사용 패딩 워드 */ 
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header - 힙의 시작을 표시하기 위함 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer - 헤더를 복사 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header - 크기가 0, 헤더만으로 구성됨. 힙이 끝났음을 알리기 위함 */
    heap_listp += (2*WSIZE); // 힙 포인터를 프롤로그 블록의 끝으로 이동시킴. (실제 데이터 블록이 시작될 위치 !)

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}


static void *extend_heap(size_t words) {
    char *bp; // 새로 할당된 힙 영역의 시작 주소를 가리키는 포인터
    size_t size; // 실제로 할당할 힙의 크기를 저장할 변수
    
    /* Allocate an even number of words to maintain alignment */
    /* 정렬을 유지하기 위해서 요청한 크기를 인접 2워드 배수(8비트)로 반올림 */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) // mem_sbrk 함수를 통해 요청한 크기만큼 힙을 확장. 이때 확장된 메모리의 시작 주소를 bp에 저장
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    /* mem_sbrk로의 모든 호출은 에필로그 블록의 헤더에 이어서 더블 워드 정렬된 메모리 블록을 리턴함 */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header - 새 가용 블록의 헤더 설정 */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer  */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header - 이 블록의 마지막 워드는 새 에필로그 블록 헤더가 된다 !! */
    
    /* Coalesce if the previous block was free */
    /* 이전 힙이 가용 블록으로 끝났다면, 두 개의 가용 블록을 통합하기 위해 coalesce 함수를 호출하고, 통합된 블록의 블록 포인터를 리턴 */
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize;
    size_t extendsize;
    char *bp;
    
    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp; 
    }
    
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
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

static void *coalesce(void *bp)  {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 헤더 위치를 바로 알 수 없으므로 풋터 사용
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0)); // 풋터는 그대로
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +  GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *find_fit(size_t asize) {
    // 힙의 시작점부터 탐색
    // alloc == 0 이고 size가 asize보다 크면 할당
    // 해당 헤더를 가리키는 포인터 반환
    void *bp = heap_listp;

    while (GET_SIZE(HDRP(bp)) > 0 ) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }
    /*
    for (bp = heap_listp; GET_SIZE(HDRP(bp) > 0; bp = NEXT_BLKP(bp))){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    */
    return NULL;
}

static void place(void *bp, size_t asize) {
    // 가용 블록의 헤더와 풋터를 alloc = 1로 만들어주기
    // 남은 부분의 크기가 최소 블록 크기와 같거나 크다면 분할. asize 만큼만 할당하고 남은 부분에 0 alloc처리 : if (current_size - asize) >= DSIZE
    // 남은 부분의 크기가 최소 블록의 크기보다 작으면 그 블록 전체(current_size)를 alloc 1 처리 (할당)

    size_t current_size = GET_SIZE(HDRP(bp));
    if ((current_size - asize) > 2*DSIZE) { //
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(current_size-asize, 0)); // 남은 공간 만큼 분할
        PUT(FTRP(bp), PACK(current_size-asize, 0));

    } else {
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1)); // a_size 아니고 current_size
    }

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) {
        return mm_malloc(size);
    }
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    
    // 기존 블록의 크기를 가져옴
    copySize = GET_SIZE(HDRP(oldptr)) //*(size_t *)((char *)oldptr - SIZE_T_SIZE); // 기존 블록 크기에서 헤더, 풋터 제외 안해줘도 되는듯
    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize); // 기존 메모리에서 새 메모리로 데이터 복사
    mm_free(oldptr);
    return newptr;
}















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

#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴

#define GET(p) (*(size_t *)(p)) // p가 참조하는 워드를 읽어서 반환.
#define PUT(p, val) (*(size_t *)(p) = (val)) // p가 가리키는 메모리 주소에 값 val을 저장

#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 헤더 또는 풋터의 size를 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) // 주소 p에 있는 헤어 또는 풋터의 할당비트를 리턴

#define HDRP(bp) ((char *)(bp) - WSIZE) // 블록 헤더를 가리키는 포인터를 리턴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 풋터를 가리키는 포인터를 리턴

#define SUCC(bp) (HDRP(bp) + WSIZE) // succ 포인터 - 다음 가용 블록을 가리키는 포인터를 리턴
#define PRED(bp) (SUCC(bp) + WSIZE) // pred 포인터 - 이전 가용 블록을 가리키는 포인터를 리턴

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 현재 블록 bp의 다음 블록의 시작 주소를 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 현재 블록 bp의 이전 블록의 시작 주소를 계산

static char *heap_listp; // 힙 포인터

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

    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding - 더블워드 경계로 정렬된 미사용 패딩 워드 */ 
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE*2, 1)); /* Prologue header - 힙의 시작을 표시하기 위함 */
    PUT(heap_listp + (2*WSIZE), NULL);
    PUT(heap_listp + (3*WSIZE), NULL);
    PUT(heap_listp + (4*WSIZE), PACK(DSIZE*2, 1)); /* Prologue footer */
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));     /* Epilogue header - 크기가 0, 헤더만으로 구성됨. 힙이 끝났음을 알리기 위함 */
    heap_listp += (2*WSIZE); // 힙 포인터를 프롤로그 블록의 끝으로 이동시킴. (실제 데이터 블록이 시작될 위치 !)

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}


static void *extend_heap(size_t words) {
    char *bp; // 새로 할당된 힙 영역의 시작 주소를 가리키는 포인터
    size_t size; // 실제로 할당할 힙의 크기를 저장할 변수
    
    /* 정렬을 유지하기 위해서 요청한 크기를 인접 2워드 배수(8비트)로 반올림 */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) // mem_sbrk 함수를 통해 요청한 크기만큼 힙을 확장. 이때 확장된 메모리의 시작 주소를 bp에 저장
        return NULL;

    /* mem_sbrk로의 모든 호출은 에필로그 블록의 헤더에 이어서 더블 워드 정렬된 메모리 블록을 리턴함 */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header - 새 가용 블록의 헤더 설정 */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer  */

    // 새 에필로그 블록 헤더 설정 - 다음 블록의 위치에서 !
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* 이전 힙이 가용 블록으로 끝났다면, 두 개의 가용 블록을 통합하기 위해 coalesce 함수를 호출하고, 통합된 블록의 블록 포인터를 리턴 */
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
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
    
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
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

    // if (prev_alloc && next_alloc) { // case 1. 전후 블록이 모두 할당 상태인 경우
    //     // 연결리스트의 맨 앞에 연결
    // heap_listp = bp;
    // }
    //else 
    if (prev_alloc && !next_alloc) { // case 2. 다음 블록만 가용 상태인 경우
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
         
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

    }
    else if (!prev_alloc && next_alloc) { // case 3. 이전 블록만 가용 상태인 경우
        remove_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

    }
    else if (!prev_alloc && !next_alloc) { // casee 4. 전후 블록이 모두 가용 상태인 경우
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +  GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
    }
    put_free_block(bp);
    return bp;
}

static void *find_fit(size_t asize) {
    // 가용 연결리스트의 시작점부터 탐색
    // size가 asize보다 크면 할당 
    // 해당 헤더를 가리키는 포인터 반환 
    
    char *bp = heap_listp;
    
    while (GET_ALLOC(HDRP(bp)) != 1) {
        if (asize <= GET_SIZE(HDRP(bp)))
            return bp;
        bp = GET(SUCC(bp)); // SUCC 자리에 저장되어 있는 주솟값으로 갱신 ;
        
    }

    return NULL;
}

static void place(void *bp, size_t asize) {
    // 남은 부분(current_size - asize)의 크기가 최소 블록 크기와 같거나 크다면 분할. 해당되는 애만 연결리스트에서 해제하고 남은 부분은 리스트에 유지하기
    // 작다면 그대로 할당 : 연결 리스트에서 해제. 앞뒤로 연결 바꿔주기 
    // 할당 블록의 헤더와 풋터를 alloc = 1로 만들어주기 
    // 만약 pred가 없었다면 (연결리스트의 첫 블록이 바뀐다면) heap_listp 갱신해주기 !! 

    size_t current_size = GET_SIZE(HDRP(bp));
    size_t remaining_size = current_size - asize;

    // 연결리스트에서 해제 
    remove_block(bp);

    if (remaining_size >= (DSIZE*2)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);

        // 분할 후 남은 부분의 헤더와 풋터에 free 처리
        PUT(HDRP(bp), PACK(remaining_size, 0));
        PUT(FTRP(bp), PACK(remaining_size, 0));

        put_free_block(bp);

    } else {
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
        
    }
}

void remove_block(void* bp) {
    char *prev_bp = GET(PRED(bp)); // 이전 블록 주소값
    char *next_bp = GET(SUCC(bp)); // 다음 블록 주소값

    if (bp == heap_listp) { // free list의 첫번째 블록 없앨 때
        PUT(PRED(next_bp), NULL);
        heap_listp = next_bp;
    } else { 
        PUT(PRED(next_bp), prev_bp);
        PUT(SUCC(prev_bp), next_bp);
    }
}

void put_free_block(void* bp) {
    PUT(SUCC(bp), heap_listp);
    PUT(PRED(bp), NULL);
    PUT(PRED(heap_listp), bp);
    heap_listp = bp;
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
    copySize = GET_SIZE(HDRP(oldptr)); //*(size_t *)((char *)oldptr - SIZE_T_SIZE); // 기존 블록 크기에서 헤더, 풋터 제외 안해줘도 되는듯
    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize); // 기존 메모리에서 새 메모리로 데이터 복사
    mm_free(oldptr);
    return newptr;
}















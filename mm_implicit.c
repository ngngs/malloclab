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
    "team_4",
    /* First member's full name */
    "ngngs",
    /* First member's email address */
    "ngng-s@hanmail.net",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE   			4   // 워드, 헤더/풋터 사이즈
#define DSIZE   			8   // 더블 워드 사이즈
#define CHUNKSIZE   		(1<<12)     // 힙 사이즈 2^12은 4kbyte는 보통 페이지 1장을 의미함.

#define MAX(x, y) 			((x) > (y) ? (x) : (y))

#define PACK(size, alloc) 	((size) | (alloc))    // |는 or연산이고, 우리가 만들 때 8의 배수로 만들어서 오른쪽 3자리를 그대로 받아오면 size와 alloc을 구분해서 받아옴

#define GET(p)  			(*(unsigned int *)(p))  //포인터 주소에 가서 word를 읽는거고
#define PUT(p, val) 		(*(unsigned int *)(p) = (val))  // 주소에 가서 값을 준다

#define GET_SIZE(p) 		(GET(p) & ~0x7) // size값이 8의 배수기 때문에, 7의 보수(2진법) 값과 받아온 GET(p)값을 and연산
#define GET_ALLOC(p)    	(GET(p) & 0x1)  // 마지막 비트의 0과 1로 할당과 가용을 판단.

#define HDRP(bp)   			((char *)(bp) - WSIZE) // 포인터 연산을 진행할 때는 받아오는 자료형(int, char 등)에 따라 값이 배수가 되어 계산된다. 그래서 char로 받으면 *1이 되어 계산, int를 주게 되면 *4가 되어 계산 
#define FTRP(bp)    		((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)   	((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;

static void *find_fit(size_t asize){    // 함수명을 포인터로 주는 이유는 뭘까? : void 포인터를 리턴하는 함수라는 뜻. 함수 명에 포인터가 붙은 게 아님.
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) { //분할 후 블록의 나머지가 최소 블록 크기와 같거나 더 크다면, 블록을 분할
        PUT(HDRP(bp), PACK(asize, 1));  // 앞에는 할당되었으니 1값을 준다
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 뒤에는 할당되지 않았으니 0값을 준다
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *coalesce(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    if (prev_alloc && next_alloc){
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + \
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *extend_heap(size_t words){ // 두 가지 경우에 호출 (1)힙이 초기화될 때 (2)malloc이 적당한 fit을 찾지 못할 때
    char *bp;
    size_t size;

    // 정렬을 유지하기 위해 2워드의 배수로 크기 할당
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)  return NULL;
    
    // 새가용블록 초기화 및 가용블록 연결
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 통합된 블록의 블록 포인터 리턴
    return coalesce(bp);
}

int mm_init(void)       // 최초 가용 블록으로 힙 생성
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;
    PUT(heap_listp, 0); //패딩 초기화
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    //머리말 헤더 초기화
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    //머리말 풋터 초기화
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        //끝부분 헤더 초기화
    heap_listp += (2*WSIZE);    

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;    // 힙을 CHUNKSIZE바이트로 확장하고 초기 가용 블록 생성 
    return 0;
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

    if (size == 0) return NULL; //거짓된 요청들(size == 0)을 무시

    //더블 워드 요건 고려
    if (size <= DSIZE)  asize = 2*DSIZE;    //8바이트는 정렬 요건 만족, 8바이트는 헤더, 풋터
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);    //8바이트를 넘는다면, 오버헤드 바이트(패딩)를 추가하고, 인접 8의 배수로 반올림

    // 크기 조정 후, 적절한 가용 블록을 가용 리스트에서 검색
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);   // 검색 성공 시, 할당기는 요청한 블록을 배치하고 옵션으로 초과부분 분할
        return bp;  // 새롭게 할당된 블록 포인터 리턴
    }

    // 크기 조정 후, 적절한 가용 블록을 찾지 못 하면, 새로운 가용 블록을 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)   return NULL;
    place(bp, asize);   // 요청한 블록을 이 새 가용 블록에 배치하고 필요 시 블록 분할
    return bp; // 새롭게 할당된 블록 포인터 리턴
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

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}















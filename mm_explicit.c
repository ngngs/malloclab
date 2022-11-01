#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "team_4",
    "ngngs",
    "ngng-s@hanmail.net",
    "",
    ""
};

// 상수 정의
#define WSIZE   			4           // 워드
#define DSIZE   			8           // 더블 워드
#define CHUNKSIZE   		(1<<12)     // 힙 사이즈 2^12은 4KB는 페이지 1장을 의미

// 매크로 정의
#define ALIGN(size)         (((size) + (0x7) & ~0x7)            // 더블워드정렬이기 때문에 size보다 큰 8의 배수로 올림
#define MAX(x, y) 			((x) > (y) ? (x) : (y))

#define PACK(size, alloc) 	((size) | (alloc))      

#define GET(p)  			(*(unsigned int *)(p))          // p 주소의 값 읽기
#define PUT(p, val) 		(*(unsigned int *)(p) = (val))  // p 주소에 val값 저장

#define GET_SIZE(p) 		(GET(p) & ~0x7)                 
#define GET_ALLOC(p)    	(GET(p) & 0x1)                  // 마지막 비트의 0과 1로 할당과 가용을 판단.

#define HDRP(bp)   			((char *)(bp) - WSIZE) 
#define FTRP(bp)    		((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)   	((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define PRED_LINK(bp)       ((char *)(bp))                  // 가용리스트에서 이전 연결 블록 정보
#define SUCC_LINK(bp)       ((char *)(bp) + WSIZE)          // 가용리스트에서 다음 연결 블록 정보

// 프로토타입 선언
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void insert_node(char *ptr);                // free()를 통해 가용블록을 가용리스트 처음 자리에 삽입(LIFO)
void remove_freenode(char *ptr);            // 가용리스트 연결 포인터 수정

static char *heap_listp = 0;                // 힙의 시작 주소
static char *root = 0;                      // 명시적 가용 리스트의 첫 노드

int mm_init(void)       // 최초 가용 블록으로 힙 생성
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;
    PUT(heap_listp, 0); //패딩 초기화
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    //머리말 헤더 초기화
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    //머리말 풋터 초기화
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        //끝부분 헤더 초기화
    root = heap_listp;
    heap_listp += (2*WSIZE);    

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;    // 힙을 CHUNKSIZE바이트로 확장하고 초기 가용 블록 생성 
    return 0;
}

static void *extend_heap(size_t words){ // 두 가지 경우에 호출 (1)힙이 초기화될 때 (2)malloc이 적당한 fit을 찾지 못할 때
    char *bp;
    size_t size;

    // 정렬을 유지하기 위해 2워드의 배수로 크기 할당
    size = (words % 2) ? (words+1) * DSIZE : words * DSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)  return NULL;
    
    // 새가용블록 초기화 및 가용블록 연결
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(SUCC_LINK(bp), 0);
    PUT(PRED_LINK(bp), 0);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 통합된 블록의 블록 포인터 리턴
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

    if (size <= 0) return NULL; //거짓된 요청들을 무시

    //더블 워드 요건 고려
    if (size <= DSIZE)  asize = 2*DSIZE;    //8바이트는 정렬 요건 만족, 8바이트는 헤더, 풋터
    else {
        asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE);
    }                                       //8바이트를 넘는다면, 오버헤드 바이트(패딩)를 추가하고, 인접 8의 배수로 반올림

    // 크기 조정 후, 적절한 가용 블록을 가용 리스트에서 검색
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);   // 검색 성공 시, 할당기는 요청한 블록을 배치하고 옵션으로 초과부분 분할
        return bp;  // 새롭게 할당된 블록 포인터 리턴
    }

    // 크기 조정 후, 적절한 가용 블록을 찾지 못 하면, 새로운 가용 블록을 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/DSIZE)) == NULL)   return NULL;
    place(bp, asize);   // 요청한 블록을 이 새 가용 블록에 배치하고 필요 시 블록 분할
    return bp; // 새롭게 할당된 블록 포인터 리턴
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(SUCC_LINK(ptr), 0);
    PUT(PRED_LINK(ptr), 0);
    coalesce(ptr);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
    }

    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));      // 현재 블록 크기에 다음 블럭 크기를 더함
        remove_freenode(NEXT_BLKP(bp));             // 가용 리스트에서 다음 블럭 연결 제거
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_freenode(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + \
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_freenode(PREV_BLKP(bp));
        remove_freenode(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp);
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size){
    if (size <= 0){
        mm_free(ptr);
        return 0;
    }

    if (ptr == NULL){
        return mm_malloc(size);
    }

    void *newp = mm_malloc(size);

    if (newp == NULL){
        return 0;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize){
        oldsize = size;
    }
    memcpy(newp, ptr, oldsize);
    mm_free(ptr);
    return newp;
}

void insert_node(char *ptr){
    char *SUCC = GET(root);
    if(SUCC != NULL){
        PUT(PRED_LINK(SUCC), ptr);
    }
    PUT(SUCC_LINK(ptr), SUCC);
    PUT(root, ptr);
}

void remove_freenode(char *ptr){
    if (GET(PRED_LINK(ptr)) == NULL){
        if (GET(SUCC_LINK(ptr)) != NULL){
            PUT(PRED_LINK(GET(SUCC_LINK(ptr))), 0);
        }
        PUT(root, GET(SUCC_LINK(ptr)));
    }
    else {
        if(GET(SUCC_LINK(ptr)) != NULL){
            PUT(PRED_LINK(GET(SUCC_LINK(ptr))), GET(PRED_LINK(ptr)));
        }
        PUT(SUCC_LINK(GET(PRED_LINK(ptr))), GET(SUCC_LINK(ptr)));
    }
    PUT(SUCC_LINK(ptr), 0);
    PUT(PRED_LINK(ptr), 0);
}

static void *find_fit(size_t asize){    // 함수명을 포인터로 주는 이유는 뭘까? : void 포인터를 리턴하는 함수라는 뜻. 함수 명에 포인터가 붙은 게 아님.
    char *addr = GET(root);
    while(addr != NULL){
        if(GET_SIZE(HDRP(addr)) >= asize){
            return addr;
        }
        addr = GET(SUCC_LINK(addr));
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    remove_freenode(bp);

    if ((csize - asize) >= (2*DSIZE)) { //분할 후 블록의 나머지가 최소 블록 크기와 같거나 더 크다면, 블록을 분할
        PUT(HDRP(bp), PACK(asize, 1));  // 앞에는 할당되었으니 1값을 준다
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 뒤에는 할당되지 않았으니 0값을 준다
        PUT(FTRP(bp), PACK(csize-asize, 0));
        PUT(SUCC_LINK(bp), 0);
        PUT(PRED_LINK(bp), 0);
        coalesce(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}















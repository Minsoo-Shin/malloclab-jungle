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
    "Minsoo Shin",
    /* First member's email address */
    "alstn5038@gamil.com",
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

// Basic constants and macros
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define INITCHUNKSIZE (1<<6)
#define LISTLIMIT 20


// calculate max value
#define MAX(x,y) ((x)>(y) ? (x) : (y))

//header, footer에 들어가는 value값을 가져온다. 
#define PACK(size,alloc) ((size)|(alloc))

//포인터 p가 가르키는 주소의 값을 가져온다.
#define GET(p) (*(unsigned int *)(p))

//포인터 p가 가르키는 곳에 val을 역참조로 갱신
#define PUT(p,val) (*(unsigned int *)(p)=(val))

//포인터 p가 가르키는 곳의 값에서 하위 3비트를 제거하여 블럭 사이즈를 반환(헤더+푸터+페이로드+패딩)
#define GET_SIZE(p) (GET(p) & ~0X7)
//포인터 p가 가르키는 곳의 값에서 맨 아래 비트를 반환하여 할당상태 판별
#define GET_ALLOC(p) (GET(p) & 0X1)

//블럭포인터를 통해 헤더 포인터,푸터 포인터 계산
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//블럭포인터 -> 블럭포인터 - WSIZE : 헤더위치 -> GET_SIZE으로 현재 블럭사이즈계산 -> 다음 블럭포인터 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
//블럭포인터 -> 블럭포인터 - DSIZE : 이전 블럭 푸터 -> GET_SIZE으로 이전 블럭사이즈계산 -> 이전 블럭포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//포인터 p가 가르키는 메모리에 포인터 ptr을 입력
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

//가용 블럭 리스트에서 next 와 prev의 포인터를 반환
#define NEXT_PTR(ptr) ((char *)(ptr))
#define PREV_PTR(ptr) ((char *)(ptr) + WSIZE)

//segregated list 내에서 next 와 prev의 포인터를 반환
#define NEXT(ptr) (*(char **)(ptr))
#define PREV(ptr) (*(char **)(PREV_PTR(ptr)))

//전역변수 
char *heap_listp = 0;
void *segregated_free_lists[LISTLIMIT];

//함수 목록
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int class;
    
    for (class = 0; class < LISTLIMIT; class++) {
        segregated_free_lists[class] = NULL;
    }
    
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;  
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;    //

    size = (words % 2) ? (words +1) * WSIZE : words * WSIZE; //더블 워드 바운더리로 정렬한 size
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    return coalesce(bp);
}

static void insert_node(void *ptr, size_t size) {
    int class = 0;
    void *search_ptr = ptr; 
    void *insert_ptr = NULL; //실제 노드가 삽입되는 위치
    
    // Select segregated list 
    while ((class < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        class++;
    }
    
    // Keep size ascending order and search
    search_ptr = segregated_free_lists[class]; // segregated_free_lists의 시작 위치를 search_ptr 변수에 대입
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = NEXT(search_ptr);
    }
    
    // Set NEXT and PREV 
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) { //Case 1: segregated_free_list[class]에 가운데 삽입할 경우
            SET_PTR(NEXT_PTR(ptr), search_ptr);
            SET_PTR(PREV_PTR(search_ptr), ptr);
            SET_PTR(PREV_PTR(ptr), insert_ptr);
            SET_PTR(NEXT_PTR(insert_ptr), ptr);
        } else { //Case 2: segregated_free_list[class]에 맨 첫 부분에 삽입할 경우
            SET_PTR(NEXT_PTR(ptr), search_ptr);
            SET_PTR(PREV_PTR(search_ptr), ptr);
            SET_PTR(PREV_PTR(ptr), NULL);
            segregated_free_lists[class] = ptr; // segregated_free_list 시작위치를 ptr에 대입
        }
    } else {
        if (insert_ptr != NULL) { //Case 3: segregated_free_list[class]에 맨 마지막에 삽입할 경우
            SET_PTR(NEXT_PTR(ptr), NULL);
            SET_PTR(PREV_PTR(ptr), insert_ptr);
            SET_PTR(NEXT_PTR(insert_ptr), ptr);
        } else { //Case 4: segregated_free_list[class] 원소가 없는 경우
            SET_PTR(NEXT_PTR(ptr), NULL);
            SET_PTR(PREV_PTR(ptr), NULL);
            segregated_free_lists[class] = ptr;
        }
    }
    
    return;
}

static void delete_node(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));
    
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    if (NEXT(ptr) != NULL) { 
        if (PREV(ptr) != NULL) { //Case 1: 삭제할 노드가 segregated_free_list[class] 가운데 있는 경우
            SET_PTR(PREV_PTR(NEXT(ptr)), PREV(ptr));
            SET_PTR(NEXT_PTR(PREV(ptr)), NEXT(ptr));
        } else { //Case 2: 삭제할 노드가 segregated_free_list[class] 맨 첫 부분에 있는 경우
            SET_PTR(PREV_PTR(NEXT(ptr)), NULL);
            segregated_free_lists[list] = NEXT(ptr);
        }
    } else {
        if (PREV(ptr) != NULL) { //Case 3: 삭제할 노드가 segregated_free_list[class] 맨 마지막에 있는 경우
            SET_PTR(NEXT_PTR(PREV(ptr)), NULL);
        } else {  //Case 4: 삭제할 노드가 segregated_free_list[class] 오직 하나의 원소일 경우
            segregated_free_lists[list] = NULL;
        }
    }
    
    return;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize; //들어갈 자리가 없을때 늘려야 하는 힙의 용량
    
    char *bp;

    /* Ignore spurious*/
    if (size == 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp; 
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

//전,후에 free block 이 있을시 합쳐줌 + 합쳐지는 경우 segregation_lists에서 기존 free block 노드 삭제해줌
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        insert_node(bp,size);
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        delete_node(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    else if (!prev_alloc && next_alloc){
        delete_node(PREV_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else{
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    
    insert_node(bp,size);
    return bp;
}

static void *find_fit(size_t asize){
    char *bp; 
    
    int class = 0; 
    size_t searchsize = asize;
    // Search for free block in segregated list
    while (class < LISTLIMIT) {
        if ((class == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[class] != NULL))) {
            bp = segregated_free_lists[class];
            // Ignore blocks that are too small or marked with the reallocation bit
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp)))))
            {
                bp = NEXT(bp);
            }
            if (bp != NULL)
                return bp;
        }
        
        searchsize >>= 1;
        class++;
    }

    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    delete_node(bp);

    if ((csize-asize)>=(2*DSIZE)){
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize,0));
        insert_node(bp,(csize-asize));
    }
    else{
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));

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
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
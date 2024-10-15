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
    "QZQ54188",
    /* First member's email address */
    "3375727892@qq.com",
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

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
//将块的大小和分配状态打包
#define PACK(size, alloc) ((size) | (alloc))

//读取与修改指针p处的值
#define GET(p)      (*(unsigned *)(p))
#define PUT(p, val) (*(unsigned *)(p) = (val))

//从头部或脚部获取大小或分配位
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

//给定块指针(有效负载指针)，得到块头部和脚部的指针
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//给定块指针(有效负载指针)，得到前面或者后面的块的块指针
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

static char *heap_list;                     //指向序言块的第二块

static void *extend_heap(size_t words);     //传入需要拓展的字节数扩展堆
static void *coalesce(void *bp);            //合并空闲块
static void *find_fit(size_t asize);        //首次适配
static void *best_fit(size_t asize);        //最佳适配
static void place(void *bp, size_t asize);  //分割空闲块

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_list = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(heap_list, 0);                              //对齐要求
    PUT(heap_list + WSIZE, PACK(DSIZE, 1));         //序言块
    PUT(heap_list + (2 * WSIZE), PACK(DSIZE, 1));   //序言块
    PUT(heap_list + (3 * WSIZE), PACK(0, 1));       //结尾块

    heap_list += DSIZE;
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL){
        return -1;
    }
    return 0;
}


static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    //双字对齐要求
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));           //用之前的结尾块设置空闲块头
    PUT(FTRP(bp), PACK(size, 0));           //设置空闲块脚
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   //空闲块的新结尾块

    return coalesce(bp);
}

static void place(void *bp, size_t asize){
    size_t size = GET_SIZE(HDRP(bp));
    if((size - asize) >= 2*DSIZE){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(size - asize, 0));
        PUT(FTRP(bp), PACK(size - asize, 0));
    }else{
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }
}

static void *coalesce(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    if(prev_alloc && next_alloc){
        //前块和后块都不是空闲块
        return bp;
    }else if(prev_alloc && !next_alloc){
        //前块不空闲后块空闲
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }else if(!prev_alloc && next_alloc){
        //后块不空闲前块空闲
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }else{
        //前后块都空闲
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *find_fit(size_t asize){
    void *bp;
    for(bp = heap_list; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if((GET_SIZE(HDRP(bp)) >= asize) && (!GET_ALLOC(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

static void *best_fit(size_t asize){
    void *bp;
    void *best_fit = NULL;
    size_t min_size = 0;
    for(bp = heap_list; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if((GET_SIZE(HDRP(bp)) >= asize) && (!GET_ALLOC(HDRP(bp)))){
            if(min_size == 0 || min_size > GET_SIZE(HDRP(bp))){
                min_size = GET_SIZE(HDRP(bp));
                best_fit = bp;
            }
        }
    }
    return best_fit;
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
    if(size == 0){
        return NULL;
    }
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }
    //找不到空间就选择拓展堆
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if(ptr == 0){
        return;
    }
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr;
    size_t copysize;

    if((new_ptr = mm_malloc(size)) == NULL){
        return 0;
    }
    copysize = GET_SIZE(HDRP(ptr));
    if(size < copysize){
        copysize = size;
    }
    memcpy(new_ptr, ptr, copysize);
    mm_free(ptr);
    return new_ptr;
}

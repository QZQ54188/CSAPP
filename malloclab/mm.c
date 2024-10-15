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
#define PUT(p, val) ((*(unsigned *)(p)) = (val))

//从头部或脚部获取大小或分配位
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

//给定块指针(有效负载指针)，得到块头部和脚部的指针
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//给定块指针(有效负载指针)，得到前面或者后面的块的块指针
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

//给定块指针，找到前驱和后继节点
#define GET_PREV(bp)    ((unsigned int *)(long)GET(bp))
#define GET_SUC(bp)     ((unsigned int *)(long)GET((unsigned int *)bp + 1))

static char *heap_list;                     //指向序言块的第二块

//给定序号，找到链表头节点的位置
#define GET_HEAD(num)   ((unsigned int *)(long)(GET(heap_list + WSIZE * num)))

#define CLASS_SIZE 20

static void *extend_heap(size_t words);     //传入需要拓展的字节数扩展堆
static void *coalesce(void *bp);            //合并空闲块
static void *find_fit(size_t asize);        //首次适配
static void *best_fit(size_t asize);        //最佳适配
static void place(void *bp, size_t asize);  //分割空闲块
static int search(size_t size);             //根据块的大小，找到头节点的位置
static void delete(void *bp);               //从相应列表中删除块
static void insert(void *bp);               //在相应列表中插入块

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_list = mem_sbrk((4 + CLASS_SIZE) * WSIZE)) == (void *)-1){
        return -1;
    }
    for(int i = 0; i < CLASS_SIZE; i++){
        PUT(heap_list + i * WSIZE, NULL);
    }
    PUT(heap_list + CLASS_SIZE * WSIZE, 0);     //对齐
    //设置序言块
    PUT(heap_list + ((1 + CLASS_SIZE) * WSIZE), PACK(DSIZE, 1));
    PUT(heap_list + ((2 + CLASS_SIZE) * WSIZE), PACK(DSIZE, 1));
    //设置结尾块
    PUT(heap_list + ((3 + CLASS_SIZE) * WSIZE), PACK(0, 1));

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

static int search(size_t size){
    int i;
    for(i = 4; i <= 22; i++){
        if(size <= (1 << i)){
            return i - 4;
        }
    }
    return i - 4;
}

static void insert(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    int num = search(size);
    //链表为空，直接放入即可
    if(GET_HEAD(num) == NULL){
        PUT(heap_list + WSIZE * num, bp);
        PUT(bp, NULL);
        PUT((unsigned int *)bp + 1, NULL);
    }else{
        //链表不为空，插入到表头
        PUT((unsigned int *)bp + 1, GET_HEAD(num)); //bp的SUC为第一个节点
        if(GET_HEAD(num) != NULL){
            PUT(GET_HEAD(num), bp);
        }
        PUT(bp, NULL);                              //bp的PREV为空
        PUT(heap_list + WSIZE * num, bp);           //头节点设置为bp
    }
}

static void delete(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    int num = search(size);
    if(GET_PREV(bp) == NULL && GET_SUC(bp) == NULL){
        //链表中唯一的节点
        PUT(heap_list + WSIZE * num, NULL);
    }else if(GET_PREV(bp) != NULL && GET_SUC(bp) == NULL){
        //最后一个节点
        PUT(GET_PREV(bp) + 1, NULL);
    }else if(GET_PREV(bp) == NULL && GET_SUC(bp) != NULL){
        //第一个节点,将头节点设置为bp的后继节点
        PUT(heap_list + WSIZE * num, GET_SUC(bp));
        PUT(GET_SUC(bp), NULL);
    }else if(GET_PREV(bp) != NULL && GET_SUC(bp) != NULL){
        //中间节点，前驱的后继设置为当前的后继，后继的前驱设置为当前的前驱
        PUT(GET_PREV(bp) + 1, GET_SUC(bp));
        PUT(GET_SUC(bp), GET_PREV(bp));
    }
}

void *coalesce(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    if(prev_alloc && next_alloc){
        //前块和后块都不是空闲块
        insert(bp);
        return bp;
    }else if(prev_alloc && !next_alloc){
        //前块不空闲后块空闲
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }else if(!prev_alloc && next_alloc){
        //后块不空闲前块空闲
        delete(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }else{
        //前后块都空闲
        delete(NEXT_BLKP(bp));
        delete(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    insert(bp);
    return bp;
}

static void place(void *bp, size_t asize){
    size_t size = GET_SIZE(HDRP(bp));

    delete(bp);
    if((size - asize) >= 2 * DSIZE){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(size - asize, 0));
        PUT(FTRP(bp), PACK(size - asize, 0));
        insert(bp);
    }else{
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }
}

static void *find_fit(size_t asize){
    int num = search(asize);
    unsigned int *bp;
    while(num < CLASS_SIZE){
        bp = GET_HEAD(num);
        while(bp != NULL){
            if(GET_SIZE(HDRP(bp)) >= asize){
                return (void *)bp;
            }
            bp = GET_SUC(bp);
        }
        num++;
    }
    return NULL;
}

static void *best_fit(size_t asize) {
    int num = search(asize);    // 从适合请求大小的链表开始查找
    unsigned int *bp;           // 指向当前空闲块
    unsigned int *best_bp = NULL; // 指向当前最合适的块
    size_t best_size = (size_t) -1; // 初始化为最大值，记录最合适的块大小

    // 遍历从当前分类及其之后的所有分类链表
    while (num < CLASS_SIZE) {
        bp = GET_HEAD(num);  // 获取当前分类链表的头指针
        
        // 遍历当前链表，查找最佳适配块
        while (bp != NULL) {
            size_t block_size = GET_SIZE(HDRP(bp)); // 获取当前块的大小

            // 如果当前块大小大于等于请求大小且更接近请求大小
            if (block_size >= asize && block_size < best_size) {
                best_size = block_size;  // 更新最佳适配块的大小
                best_bp = bp;            // 更新最佳适配块的指针
            }

            bp = GET_SUC(bp);  // 继续查找下一个块
        }
        
        num++;  // 继续查找下一个分类的链表
    }

    return (void *)best_bp; // 返回最适合的块，或者如果没找到则返回 NULL
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
    if((bp = best_fit(asize)) != NULL){
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

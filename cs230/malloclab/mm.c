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


#define is_print 1


#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros for manipulating the free list */
#define WSIZE   4 // Word and headr/footer size (bytes)
#define DSIZE   8 // Double word size (bytes)
#define CHUNKSIZE   (1<<12) // Extend heap by this amount (bytes)

#define MAX(x,y) (x>y?x:y)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)  (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define PUTA(p, val) (*(char **)(p) = (char *)(val))

/* Read the size and allocated field from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of nextand previous linked blocks address*/
#define NEXTP(bp)   ((char **)(bp))
#define PREVP(bp)   ((char **)(bp) + 8)

/* Given block ptr bp, compute address of next and previous linked blocks */
#define NEXT_BLL(bp)   ((char *)(*NEXTP(bp)))
#define PREV_BLL(bp)   ((char *)(*PREVP(bp)))


static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void push_link(void *bp, void *ibp);
static void remove_link(void *bp);

static void *heap_listp;
char *first_linkp;
char *last_linkp;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if (is_print)
        printf("i");
    /* Create the initial empty heap */
    if((heap_listp = mem_sbrk((2*DSIZE)+4*WSIZE)) == (void *)-1){
        printf("\nreturn -1\n");
        return -1;
    }
    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(3*DSIZE, 1));    /* Prologue header */
    PUT(heap_listp + (2*DSIZE) +(2*WSIZE), PACK(3*DSIZE, 1));    /* Prologue footer */
    PUT(heap_listp + (2*DSIZE) +(3*WSIZE), PACK(0, 1));        /* Epilogue header */
    heap_listp += (2*WSIZE);
    first_linkp = heap_listp;
    last_linkp = heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        printf("\nreturn -1\n");
        return -1;
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    if (is_print)
        printf("\nm\n");
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignement reqs. */
    if(size <= 2*DSIZE)
        asize = 4*DSIZE;
    else
        asize = DSIZE * ((size + (3*DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    /* No fit found, Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if (is_print)
        printf("\nf%p\n",bp);
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    if(first_linkp == NULL){
        printf("\nfree :0\n");
        first_linkp = bp;
        last_linkp = bp;
    }
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    if (is_print)
        printf("r");
    void *oldbp = bp;
    void *newbp;
    size_t copySize;
    
    newbp = mm_malloc(size);
    if (newbp == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(bp));
    if (size < copySize)
      copySize = size;
    memcpy(newbp, oldbp, copySize);
    mm_free(oldbp);
    return newbp;
}


static void *extend_heap(size_t words)
{
    if (is_print)
        printf("e");
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if((long)(bp  = mem_sbrk(size)) == -1)
        return NULL;
    if(size<4*DSIZE){
        printf("extend size is to small!!\n");
    }
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));       /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));       /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    bp = coalesce(bp);

    /* Coalesce if the previous block was free */
    return bp;
}

static void *coalesce(void *bp)
{
    if (is_print)
        printf("c");
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){           /* Case 1 */
            push_link(first_linkp, bp);
            ////
            return bp;
    }

    else if (prev_alloc && !next_alloc){    /* Case 2 */
        remove_link(NEXT_BLKP(bp));
        push_link(first_linkp, bp);
        /////
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc){    /* Case 3 */
        remove_link(PREV_BLKP(bp));
        push_link(first_linkp, PREV_BLKP(bp));
        ////
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                  /* Case 4 */
        remove_link(PREV_BLKP(bp));
        remove_link(NEXT_BLKP(bp));
        push_link(first_linkp, PREV_BLKP(bp));
        ///
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }


    return bp;
}

static void *find_fit(size_t asize)
{
    if (is_print)
        printf("i");

    /* First-fit search */
    char *bp;

    bp = first_linkp;
    if(bp == last_linkp){
        return NULL;
    }
    bp = NEXT_BLL(bp);
    while(bp!=NULL){
        if(asize<= GET_SIZE(HDRP(bp))){
            return bp;
        }
        if(bp == last_linkp){
            return NULL;
        }
        bp = NEXT_BLL(bp);
    }
    return NULL; 
}

static void place(void *bp, size_t asize)
{
    if (is_print)
        printf("p");
    size_t csize= GET_SIZE(HDRP(bp));
    char *oldbp = bp;
    char *newbp;
    if((csize - asize) >= (4*DSIZE)) {
        PUT(HDRP(oldbp), PACK(asize, 1));
        PUT(FTRP(oldbp), PACK(asize, 1));
        newbp = NEXT_BLKP(oldbp);
        if (is_print)
            printf("newbp%p:size:%d",newbp,asize);
        PUT(HDRP(newbp), PACK(csize-asize, 0));
        PUT(FTRP(newbp), PACK(csize-asize, 0));
        if(oldbp == first_linkp && oldbp == last_linkp){
            first_linkp = newbp;
            last_linkp = newbp;
        }
        else if(oldbp == first_linkp){
            PUTA(NEXTP(newbp), NEXT_BLL(oldbp));
            PUTA(PREVP(NEXT_BLL(oldbp)), newbp);
            first_linkp = newbp;

        }
        else if(oldbp == last_linkp){
            PUTA(NEXTP(PREV_BLL(oldbp)), newbp);
            PUTA(PREVP(newbp), PREV_BLL(oldbp));
            last_linkp = newbp;
        }
        else{
            PUTA(NEXTP(PREV_BLL(oldbp)), newbp);
            PUTA(NEXTP(newbp), NEXT_BLL(oldbp));
            PUTA(PREVP(NEXT_BLL(oldbp)), newbp);
            PUTA(PREVP(newbp), PREV_BLL(oldbp));
        }

    }
    else{
        PUT(HDRP(oldbp), PACK(csize, 1));
        PUT(FTRP(oldbp), PACK(csize, 1));
        remove_link(oldbp);
    }
}

static void push_link(void *bp, void *ibp)
{
    if(is_print)
        printf("l");
    if (bp == NULL && first_linkp == NULL){
        first_linkp = bp;
        last_linkp = bp;
    }
    else if(bp == last_linkp){
        PUTA(NEXTP(bp), ibp);
        PUTA(PREVP(ibp), bp);
        last_linkp = ibp;
    }
    else{
        PUTA(NEXTP(ibp), NEXT_BLL(bp));
        PUTA(NEXTP(bp), ibp);
        PUTA(PREVP(NEXT_BLL(ibp)), ibp);
        PUTA(PREVP(ibp), bp);
    }
}

/* when remove given bp's block, straigten prev, next block's links */
static void remove_link(void *bp)
{
    if(is_print)
        printf("m");
    if(bp == first_linkp && bp == last_linkp){
        if (is_print)
            printf("remove link with null!!!!!!");
        first_linkp = NULL;
        printf("\n!\n");
        last_linkp = NULL;
    }
    else if(bp == first_linkp){
        first_linkp = NEXT_BLL(bp);

    }
    else if(bp == last_linkp){
        last_linkp = PREV_BLL(bp);
    }
    else{
        PUTA(NEXTP(PREV_BLL(bp)), NEXT_BLL(bp));
        PUTA(PREVP(NEXT_BLL(bp)), PREV_BLL(bp));
    }


}

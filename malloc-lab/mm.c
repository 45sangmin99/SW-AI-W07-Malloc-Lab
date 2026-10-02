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
#include <stdint.h> //uint32_t 써야함..

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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * mm_init - initialize the malloc package.
 */

#define MAX(a, b) ((a) > (b) ? (a) : (b))

#define HEADER(bp) (*(uint32_t *)(bp))
#define FOOTER(bp, size) (*(uint32_t *)((char *)(bp) + (size) - 4))

#define SIZE(bp) (*(uint32_t *)(bp)&~0b111)
#define FLAG(bp) (*(uint32_t *)(bp)&0b1)

#define PREV_OFF(bp) (*(uint32_t *)((char *)(bp) + 4))
#define NEXT_OFF(bp) (*(uint32_t *)((char *)(bp) + 8))

#define PREV_PTR(bp) (PREV_OFF(bp) ? (uint32_t *)(base_ptr + PREV_OFF(bp)) : NULL)
#define NEXT_PTR(bp) (NEXT_OFF(bp) ? (uint32_t *)(base_ptr + NEXT_OFF(bp)) : NULL)

typedef struct {
    uint32_t size;
    uint32_t head;
} Class;

static Class *classes;
static char* base_ptr;

#define CLASS_COUNT 16
#define CLASS_SIZES \
    16, 32, 48, 64, 80, 96, 112, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768

#define CHUNKSIZE 4096

 /* 
 *
 * Allocated Block
 * -------------------------------------------------------------------------
 * |                          size                          |    x 0 x     |
 * -------------------------------------------------------------------------
 * |                                                                       |
 * ------------------------------------------------------------------------- 
 * 
 * Free Block
 * -------------------------------------------------------------------------
 * |                          size                          |    x 0 x     |
 * -------------------------------------------------------------------------
 * |                                 prev                                  |
 * -------------------------------------------------------------------------
 * |                                 next                                  |
 * -------------------------------------------------------------------------
 * |                                                                       |
 * -------------------------------------------------------------------------
 * |                          size                          |    x 0 x     |
 * -------------------------------------------------------------------------
 *
 * Free Block(8 or 16)
 * -------------------------------------------------------------------------
 * |                          size                          |    x 0 x     |
 * -------------------------------------------------------------------------
 * |                          size                          |    x 0 x     |
 * -------------------------------------------------------------------------
 *
 * 000 = prev free
 * 001 = prev alloc
 * 
 * prev, next는 기준점 기반의 uint32_t로 해서 찾아가기.
 * 0이면 NULL
 * 
 */

int mm_init(void){
    size_t sizes[CLASS_COUNT] = {CLASS_SIZES};
    classes = mem_sbrk(sizeof(Class) * CLASS_COUNT);
    base_ptr = mem_heap_lo();

    for (int i = 0; i < CLASS_COUNT; i++){
        classes[i].size = sizes[i];
        classes[i].head = 0;
    }

    char *temp = mem_sbrk(8);
    *(uint32_t *)temp = 0b1; //프롤로그
    *(uint32_t *)(temp+4) = 0b1; //에필로그
    return 0;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

unsigned int get_index(size_t size){
    int left = 0;
    int right = CLASS_COUNT - 1;
    int idx = 0;
    
    size = ALIGN(size);

    while(left <= right){
        int mid = (left + right) / 2;
        if (classes[mid].size <= size){
            idx = mid;
            left = mid + 1;
        }else{
            right = mid - 1;
        }
    }
    return idx;
}

void insert_node(char *ptr){
    int idx = get_index(SIZE(ptr));
    uint32_t old_head = classes[idx].head;
    if(old_head)PREV_OFF(base_ptr + old_head) = ptr - base_ptr;
    PREV_OFF(ptr) = 0;
    NEXT_OFF(ptr) = old_head;
    classes[idx].head = ptr - base_ptr;
}

void remove_node(char *ptr){
    if(PREV_PTR(ptr)){
        NEXT_OFF(PREV_PTR(ptr)) = NEXT_OFF(ptr);
    }else{
        int idx = get_index(SIZE(ptr));
        classes[idx].head = NEXT_OFF(ptr);
    }
    if(NEXT_PTR(ptr)) PREV_OFF(NEXT_PTR(ptr)) = PREV_OFF(ptr);
}

char* coalesce(char *block_ptr){
    u_int32_t flag = FLAG(block_ptr);
    u_int32_t size = SIZE(block_ptr);
    u_int32_t next_size = SIZE(block_ptr + size);
    u_int32_t prev_size = SIZE(block_ptr - 4);;
    if(next_size && !(HEADER(block_ptr + size + next_size) & 0b1)){
        if(next_size >= 16)remove_node(block_ptr + size);
        size += next_size;
        HEADER(block_ptr) = size | flag;
    }
    if(!(HEADER(block_ptr) & 0b1)){
        size += prev_size;
        block_ptr -= prev_size;
        if(prev_size >= 16)remove_node(block_ptr);
        HEADER(block_ptr) = size | 0b1;
    }
    FOOTER(block_ptr, size) = size | 0b1;
    insert_node(block_ptr);
    return block_ptr;
};

void split_block(char *block_ptr, uint32_t total_size, uint32_t new_size){
    uint32_t flag = FLAG(block_ptr);
    uint32_t remain = total_size - new_size;

    HEADER(block_ptr) = new_size | flag;    
    if(remain == 0){
        HEADER(block_ptr + new_size) |= 0b1;
    }else if(remain < 16){
        HEADER(block_ptr + new_size) = remain | 0b1;
        FOOTER(block_ptr + new_size, 8) = remain | 0b1;
    }else{
        uint32_t index = get_index(remain);

        HEADER(block_ptr + new_size) = remain | 0b1;
        PREV_OFF(block_ptr + new_size) = 0;
        NEXT_OFF(block_ptr + new_size) = classes[index].head;
        FOOTER(block_ptr + new_size, remain) = remain | 0b1;

        insert_node(block_ptr + new_size);
    }
}

void *mm_malloc(size_t size){
    //TODO: 4일 때 푸터 사라지니까 패딩 없이 정렬함으로써 용량을 더 절약할 수 있..나? 고민이 필요함.
    size_t block_size = ALIGN(size + 4); //헤더 들어가야하니까
    uint32_t block_offset = 0;
    size_t remain = 0;
    
    int idx = get_index(block_size);

    char *block_ptr = NULL;
    for (int i = idx; i < CLASS_COUNT && block_ptr == NULL; i++){
        uint32_t offset = classes[i].head;
        uint32_t *candidate_ptr = offset ? (uint32_t *)(base_ptr + offset) : NULL;
        while(candidate_ptr){
            uint32_t candidate_size = *candidate_ptr;
            if(candidate_size >= block_size){
                block_ptr = (char*)candidate_ptr;
                remove_node(block_ptr);
                break;
            }
            candidate_ptr = NEXT_PTR(candidate_ptr);
        }
    }
    if(block_ptr){
        size_t total_size = HEADER(block_ptr) & ~0b111;
        block_offset = block_ptr - base_ptr;
        remain = total_size - block_size;
        HEADER(block_ptr) = block_size|0b1; // 헤더
    }else{
        size_t extend_size = MAX(block_size, CHUNKSIZE);
        block_ptr = (char*)mem_sbrk(extend_size) - 4;
        remain = extend_size - block_size;
        uint32_t prev_alloc = FLAG(block_ptr); // 원래 이전 점유되어 있었는지 체크
        if(!prev_alloc){
            uint32_t prev_size = SIZE(block_ptr - 4);
            char *prev_ptr = block_ptr - prev_size;
            if(prev_size >= 16)
                remove_node(prev_ptr);
            block_ptr = prev_ptr;
            extend_size += prev_size;
            remain += prev_size;
            prev_alloc = FLAG(block_ptr);
        }
        HEADER(block_ptr) = (uint32_t)block_size | prev_alloc;
        block_offset = (uint32_t)(block_ptr - base_ptr);
        *(uint32_t *)(block_ptr + extend_size) = 0b0; // 에필로그
    }
    split_block(block_ptr, block_size + remain, block_size);
    return (char *)block_ptr + 4;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr){
    ptr -= 4;
    uint32_t size = SIZE(ptr);
    HEADER(ptr + size) &= ~0b1;
    ptr = coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *old_ptr = ptr-4;
    void *new_ptr;
    size_t old_size = SIZE(old_ptr);
    size_t new_size = ALIGN(size+4);
    if (old_size > new_size){
        uint32_t remain = old_size - new_size;
        split_block(old_ptr, old_size, new_size);
        return ptr;
    } else if (old_size == new_size){
        return ptr;
    } else if (SIZE(old_ptr + old_size) && FLAG(old_ptr + old_size + SIZE(old_ptr + old_size)) == 0 && old_size + SIZE(old_ptr + old_size) >= new_size){
        uint32_t total_size = old_size + SIZE(old_ptr + old_size);
        if(SIZE(old_ptr + old_size) >= 16) remove_node(old_ptr + old_size);
        split_block(old_ptr, total_size, new_size);
        return ptr;
    }

    new_ptr = mm_malloc(size);

    size_t copy_size = old_size - 4;
    if(size < copy_size)copy_size = size;
    memcpy(new_ptr, ptr, copy_size);
    mm_free(ptr);

    return new_ptr;
}
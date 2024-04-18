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
    "team 7",
    /* First member's full name */
    "Donghwan Choi",
    /* First member's email address */
    "cdhcsh@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* 기본 사이즈 지정*/
#define WSIZE 4             /* 워드와 header,footer 사이즈 (bytes)*/
#define DSIZE 8             /* double word (bytes) */
#define CHUNKSIZE (1 << 10) /* 확장될 힙의 크기 (bytes)*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 사이즈와 할당 비트 입력*/
#define PACK(size, alloc) ((size) | (alloc))

/* p의 주소값을 읽거나 씀*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* GET_SIZE : header,footer 로부터 사이즈를 읽음 */
#define GET_SIZE(p) (GET(p) & ~0x7)
/* GET_ALLOC : header,footer 로부터 할당비트를 읽음*/
#define GET_ALLOC(p) (GET(p) & 0x1)

/* HDRP : 주소 p의 header를 가리키는 포인터 반환*/
#define HDRP(p) ((char *)(p)-WSIZE)
/* FTRP : 주소 p의 footer를 가리키는 포인터 반환*/
#define FTRP(p) ((char *)(p) + GET_SIZE(HDRP(p)) - DSIZE)

/* NEXT_BLKP : 다음 블록의 블록 포인터 반환*/
#define NEXT_BLKP(p) ((char *)(p) + GET_SIZE(HDRP(p)))
/* PREV_BLKP : 이전 블록의 블록 포인터 반환*/
#define PREV_BLKP(p) ((char *)(p)-GET_SIZE(((char *)(p)-DSIZE)))

/* 다음 가용 블록의 주소*/
#define GET_SUCC(p) (*(char **)(p + WSIZE))
/* 이전 가용 블록의 주소*/
#define GET_PRED(p) (*(char **)(p))

/* 분리된 가용리스트 수 */
#define MAX_SEGREGATED_LIST_SIZE 12

/* class에 따른 루트 주소 */
#define GET_ROOT(class) (*(char **)(seg_listp + (WSIZE * (class))))

/* class에 따른 블록 크기*/
#define GET_BLOCK_SIZE(class) (1 << (5 + class))

/* 함수 프로토타입 선언*/
static void *_extend_heap(size_t words);
static void *_coalesce(void *p);
static char *_find_fit(size_t size);
static void _place(void *p, size_t size);
static void _remove_free_block(void *p);
static void _add_free_block(void *p);
static int _get_class(size_t size);
static int _get_block_size(size_t size);

static char *heap_listp; /* prologue 를 가리킴*/
static char *seg_listp;

/* 힙 확장*/
static void *_extend_heap(size_t words)
{
    char *p;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if (size < 2 * DSIZE)
        size = 2 * DSIZE;

    if ((long)(p = mem_sbrk(size)) == -1) //
        return NULL;

    PUT(HDRP(p), PACK(size, 0));         /* Free block header */
    PUT(FTRP(p), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(p)), PACK(0, 1)); /* New epilogue header -새로운 끝 설정 */

    return _coalesce(p);
}

/* 블럭 할당 해제 및 병합 */
static void *_coalesce(void *p)
{
    /*
    case 1: 이전과 다음 블록 모두 할당된 상태 -> 통합 종료
    case 2: 이전 블록은 할당되있고 다음블록은 가용상태 -> 현재 블록을 다음 리스트와 연결함
    case 3: 이전 블록은 가용상태, 다음블록은 할당상태 -> 현재 블록을 이전 리스트와 연결함
    case 4: 이전과 다음 블록 모두 가용상태 -> 이전,현재,다음 블록을 연결
    */

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(p)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(p)));
    size_t size = GET_SIZE(HDRP(p));

    if (prev_alloc && !next_alloc)
    { // case 2
        _remove_free_block(NEXT_BLKP(p));
        size += GET_SIZE(HDRP(NEXT_BLKP(p)));
        PUT(HDRP(p), PACK(size, 0));
        PUT(FTRP(p), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { // case 3
        _remove_free_block(PREV_BLKP(p));
        p = PREV_BLKP(p);
        size += GET_SIZE(HDRP(p));
        PUT(HDRP(p), PACK(size, 0));
        PUT(FTRP(p), PACK(size, 0));
    }
    else if (!prev_alloc && !next_alloc)
    { // case 4
        _remove_free_block(PREV_BLKP(p));
        _remove_free_block(NEXT_BLKP(p));
        size += GET_SIZE(HDRP(NEXT_BLKP(p))) + GET_SIZE(HDRP(PREV_BLKP(p)));
        p = PREV_BLKP(p);
        PUT(HDRP(p), PACK(size, 0));
        PUT(FTRP(p), PACK(size, 0));
    }
    _add_free_block(p);
    return p;
}

/* 가용블럭 탐색 */
static char *_find_fit(size_t size)
{
    int class = _get_class(size);
    void *p;
    while (class < MAX_SEGREGATED_LIST_SIZE)
    {
        p = GET_ROOT(class);
        while (p != NULL)
        {
            if (size <= GET_SIZE(HDRP(p)))
                return p;
            p = GET_SUCC(p);
        }
        class += 1;
    }
    return NULL;
}

/* 가용블록 연결 리스트에 p 블록을 제거*/
static void _remove_free_block(void *p)
{
    int class = _get_class(GET_SIZE(HDRP(p)));
    if (p == GET_ROOT(class))
    {
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class));
        return;
    }
    GET_SUCC(GET_PRED(p)) = GET_SUCC(p);
    if (GET_SUCC(p) != NULL)
        GET_PRED(GET_SUCC(p)) = GET_PRED(p);
}

/* 가용블록 연결 리스트에 p 블록을 추가*/
static void _add_free_block(void *p)
{
    int class = _get_class(GET_SIZE(HDRP(p)));
    GET_SUCC(p) = GET_ROOT(class);
    if (GET_ROOT(class) != NULL)
        GET_PRED(GET_ROOT(class)) = p;
    GET_ROOT(class) = p;
}

/* 가용블럭에 size만큼 할당 */
static void _place(void *p, size_t size)
{
    size_t c_size = GET_SIZE(HDRP(p)); // 현재 블록의 크기

    _remove_free_block(p); // 가용블록 연결 리스트에서 제거

    if ((c_size - size) >= (2 * DSIZE))
    { /* 할당 후 남은 공간이 최소 블록 크기 이상이라면 분할함*/
        PUT(HDRP(p), PACK(size, 1));
        PUT(FTRP(p), PACK(size, 1));

        p = NEXT_BLKP(p);

        PUT(HDRP(p), PACK(c_size - size, 0));
        PUT(FTRP(p), PACK(c_size - size, 0));

        _add_free_block(p); // 남은 블록을 가용블록 연결 리스트에 추가
    }
    else
    {
        PUT(HDRP(p), PACK(c_size, 1));
        PUT(FTRP(p), PACK(c_size, 1));
    }
}

int _get_class(size_t size)
{
    int class = -4;
    while (size > 0 && class < 12)
    {
        class += 1;
        size >>= 1;
    }
    if (class > (MAX_SEGREGATED_LIST_SIZE - 1))
        class = MAX_SEGREGATED_LIST_SIZE - 1;
    return MAX(class - 1, 0);
}
int _get_block_size(size_t size)
{
    int b_size = 1;
    while (b_size < size)
    {
        b_size *= 2;
    }
    return b_size;
}
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk((MAX_SEGREGATED_LIST_SIZE + 4) * WSIZE)) == (void *)-1)
        return -1;
    size_t size = (MAX_SEGREGATED_LIST_SIZE + 2) * WSIZE;
    PUT(heap_listp, 0);                           /* 정렬 패딩 */
    PUT(heap_listp + (1 * WSIZE), PACK(size, 1)); /* 프롤로그 header */
    for (int i = 0; i < MAX_SEGREGATED_LIST_SIZE; i++)
        PUT(heap_listp + ((i + 2) * WSIZE), NULL);
    PUT(heap_listp + ((MAX_SEGREGATED_LIST_SIZE + 2) * WSIZE), PACK(size, 1)); /* 프롤로그 footer */
    PUT(heap_listp + ((MAX_SEGREGATED_LIST_SIZE + 3) * WSIZE), PACK(0, 1));    /* 에필로그 header */
    heap_listp += (2 * WSIZE);                                                 /* 초기 가용 블록의 p*/
    seg_listp = heap_listp;

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
    char *p;

    if (size == 0)
        return NULL;

    if (size <= CHUNKSIZE)
    {
        size = _get_block_size(size);
    }
    if (size <= DSIZE)
        asize = 2 * DSIZE; /*헤더, 풋터 포함하려고 더블워드 2배*/
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((p = _find_fit(asize)) != NULL)
    {
        _place(p, asize);
        return p;
    }

    /* 맞는 블록이 없으면 힙 영역을 확장하고 요청 블록을 새 가용 블록에 배치 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((p = _extend_heap(asize / WSIZE)) == NULL)
        return NULL;
    _place(p, asize);
    return p;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *p)
{
    size_t size = GET_SIZE(HDRP(p));

    PUT(HDRP(p), PACK(size, 0));
    PUT(FTRP(p), PACK(size, 0));
    _coalesce(p);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *p, size_t size)
{
    if (size <= 0)
    {
        mm_free(p);
        return 0;
    }
    if (p == NULL)
        return mm_malloc(size);

    size_t new_size = size + 2 * WSIZE;
    size_t old_size = GET_SIZE(HDRP(p));
    size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(p)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(p)));
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(p)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(p)));
    size_t c_size;

    if (new_size <= old_size)
        return p;
    if (!prev_alloc && new_size <= (c_size = old_size + prev_size))
    {
        char *pre = PREV_BLKP(p);
        _remove_free_block(pre);
        memmove(pre, p, old_size);
        PUT(HDRP(pre), PACK(c_size, 1));
        PUT(FTRP(pre), PACK(c_size, 1));
        return pre;
    }
    if (!next_alloc && new_size <= (c_size = old_size + next_size))
    {
        _remove_free_block(NEXT_BLKP(p));

        PUT(HDRP(p), PACK(c_size, 1));
        PUT(FTRP(p), PACK(c_size, 1));
        return p;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return 0;
    memcpy(newptr, p, old_size);
    mm_free(p);
    return newptr;
}

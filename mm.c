/* mm-naive.c - The fastest, least memory-efficient malloc package.
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free. */
/* NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 * okok let go */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

// team - info
team_t team = {
    "team 932",
    "jayK",
    "jayK.com",
    "",
    ""};

////////////////////////////변수시작/////////////////////////////////////

// 전처리기 매크로 할당
#define wsize 4                           // 워드는 4바이트
#define dsize 8                           // 더블워드는 8바이트
#define max(x, y) ((x) > (y) ? (x) : (y)) // x,y중 max값
// 청크크기 줄이면 util이 올라가네?
#define chunksize (1 << 9) // 청크 하나에 4KB할당(페이지 크기랑 일치해서 편할듯)

// 크기와 가용여부를 합쳐서(비트연산 활용) 표시함
#define pack(size, alloc) ((size) | (alloc)) // or연산으로 헤더에서 쓸 word만들어줌

// 주소p에 r/w
#define get(p) (*(unsigned int *)(p))                   // 포인터로 주소p를 참조, 블록 이동할 때 쓸거
#define put(p, val) (*(unsigned int *)(p) = (int)(val)) // 주소 p에 val이라는 주소를 담음

// 주소p에서 크기와 할당여부를 읽어옴
#define get_size(p) (get(p) & ~0x7) // &와 ~를 이용해 뒷 3자리를 제외한 비트를 가져옴
#define get_alloc(p) (get(p) & 0x1) // 0번째 비트(할당여부)를 가져옴

// 기본 이동
#define header_of(bp) ((char *)(bp)-wsize)                             // header 포인터
#define footer_of(bp) ((char *)(bp) + get_size(header_of(bp)) - dsize) // FooTer 포인터
#define prev_block(bp) ((char *)(bp)-get_size((char *)(bp)-dsize))     // 이전블록으로 ㄲㄲ
#define next_block(bp) ((char *)(bp) + get_size((char *)(bp)-wsize))   // 다음블럭으로 ㄱㄱ

// 가용 리스트 내 이동
// prev/next 블록이 가리키는 곳으로 가는 이중포인터 //void*의 값에 *접근함
#define prev_freep(bp) (*(void **)(bp))         // prev free ㄱㄱ
#define next_freep(bp) (*(void **)(bp + wsize)) ////next free ㄱㄱ

// (seglist) 자신의 power에 맞는 가용블럭 찾음
// 크기 2^4면 (heaplistp+wsize*2)만큼 가는식
#define find_freep(power) (*(void **)((char *)(heap_listp) + (wsize * (power + 1))))
// #define find_freep(power) (*(void **)((heap_listp) + (wsize * power))) // hp가 이미 char인데 왜 char로 또 형변환하는거임??

#define power_size (10) // free list를 (2^4)부터 (2^12 ~ beyond)까지 9개 만들겠다

static char *heap_listp; // 초기 힙 시작 포인터
////////////////////////////함수선언/////////////////////////////////////
int mm_init(void);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
void *mm_realloc(void *bp, size_t size);
void mm_free(void *bp);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
void del_freesign(void *bp);
void make_freesign(void *bp);
int find_power(size_t size);

////////////////////////////함수시작/////////////////////////////////////

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(14 * wsize)) == (void *)-1)
        return -1;

    put(heap_listp, 0);                                 // 블록 생성 시 패딩
    put(heap_listp + (1 * wsize), pack(12 * wsize, 1)); // 프롤로그 헤더

    char *current_ptr = heap_listp + (2 * wsize); // power의 초기 블록 포인터 설정
    for (int i = 0; i < power_size; i++)          // power_size만큼 블록생성
    {
        put(current_ptr, NULL); // 초기 블록 설정
        current_ptr += wsize;   // 주소 증가
    }

    put(current_ptr, pack(12 * wsize, 1)); // 프롤로그 푸터
    put(current_ptr + wsize, NULL);        // 에필로그 헤더

    if (extend_heap(chunksize / wsize) == NULL) // 초기 힙 확장
        return -1;

    return 0;
}

// heap 확장함(sbrk처럼), 인수 words인거 확인
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size; // unsigned int

    // 더블워드 정렬위해 짝수로 만들어서 alloc
    size = (words % 2) ? (words + 1) * wsize : words * wsize;
    if ((bp = mem_sbrk(size)) == (void *)-1) // heap크기 size만큼 늘리고 bp 이동시킴.
        return NULL;                         // 사이즈 늘릴 때마다 old brk -> sbrk로 갱신(함수 내부 참조)

    // 생성한 free-heap space에 헤더, 푸터만들고 에필로그헤더 갱신
    put(header_of(bp), pack(size, 0));
    put(footer_of(bp), pack(size, 0));
    put(header_of(next_block(bp)), pack(0, 1));

    // 만든 free space를 주변 블록과 합침
    return coalesce(bp);
}

////////////////////////////coalesce/////////////////////////////////////
static void *coalesce(void *bp) // 앞 뒤 가용블럭과 free한 블럭 합칩
{
    // 앞 뒤 블럭의 free 여부 확인
    size_t prev_alloc = get_alloc(footer_of(prev_block(bp)));
    size_t next_alloc = get_alloc(header_of(next_block(bp)));
    size_t size = get_size(header_of(bp));

    if (prev_alloc && next_alloc)
    {
    }

    // 앞뒤 중 가용상태인것과 합침
    else if (prev_alloc && !next_alloc) // 다음 블럭이 가용일때
    {
        del_freesign(next_block(bp)); // 다음 블럭 freesign 지움
        size += get_size(header_of(next_block(bp)));
        put(header_of(bp), pack(size, 0)); // 헤더에 증가한 사이즈 입력
        put(footer_of(bp), pack(size, 0)); // 다음블럭의 footer 가리킴
    }

    else if (!prev_alloc && next_alloc) // 이전 블록이 가용일때
    {
        del_freesign(prev_block(bp));
        bp = prev_block(bp); // bp를 원 prev의 헤더로 옮김
        size += get_size(header_of(bp));
        put(header_of(bp), pack(size, 0)); // prev의 헤더에 put
        put(footer_of(bp), pack(size, 0)); // prev의 푸터에 put
    }

    else // 둘 다 가용일때
    {
        del_freesign(prev_block(bp));
        del_freesign(next_block(bp));
        size += get_size(header_of(prev_block(bp))) + get_size(footer_of(next_block(bp)));
        bp = prev_block(bp);               // bp를 원 prev의 헤더로 옮김
        put(header_of(bp), pack(size, 0)); // prev의 헤더에 put
        put(footer_of(bp), pack(size, 0)); // prev의 푸터에 put
    }
    make_freesign(bp); // bp에 freesign 만듦
    return bp;
}

// 메모리 할당함
void *mm_malloc(size_t size)
{
    size_t asize;       // 블록 사이즈 조정(adjust)
    size_t extend_size; // fit없으면 extend로 넘기기 위한 var
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= 1 * dsize) // malloc받은 사이즈가 작아서 헤더푸터,prev,next 안들어가면
        asize = 2 * dsize; // asize에 헤더푸터,prev,next 사이즈(24Byte) 넣음
    else                   // 무조건 자기보다 큰 8의 배수 중 가장 작은값으로 바꿈
        asize = dsize * ((size + (dsize) + (dsize - 1)) / dsize);

    bp = find_fit(asize); // asize 정하고나서 bp에 반영함
    if (bp != NULL)       // fit to asize 찾아서 place
    {
        place(bp, asize);
        return bp;
    }

    // if통과 못하면 size extend하고 다시 place
    extend_size = max(asize, chunksize); // chunksize=4KB(initial val)
    if ((bp = extend_heap(extend_size / wsize)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize) // first fit
{
    void *bp;
    int power = find_power(asize);
    if (power == -1)
        return NULL;

    for (power; power <= power_size; power++)
    {
        bp = find_freep(power);
        while (bp != NULL)
        {
            if (asize <= get_size(header_of(bp)))
                return bp;
            bp = next_freep(bp);
        }
    }

    return NULL;
}

static void place(void *bp, size_t asize) // find한 bp, asize 넣어서 place함
{
    size_t curr_size = get_size(header_of(bp));
    del_freesign(bp);

    if ((curr_size - asize) >= (2 * dsize)) // 현재 size-받은 size해서 헤더+푸터+prev,next의 size보다 크면
    {                                       // 다음블럭에 H F P N 만듦
        put(header_of(bp), pack(asize, 1)); // asize만큼 떨어진 헤더 푸터
        put(footer_of(bp), pack(asize, 1)); // 둘다 채우고

        bp = next_block(bp);                            // 다음블럭으로 가서
        put(header_of(bp), pack(curr_size - asize, 0)); // 남은 부분 헤더 푸터 만듦
        put(footer_of(bp), pack(curr_size - asize, 0));

        make_freesign(bp); // freesign만들고
    }
    else // 헤더 푸터 못들어가는 곳이면 그냥 curr 다 채움
    {
        put(header_of(bp), pack(curr_size, 1));
        put(footer_of(bp), pack(curr_size, 1));
    }
}

// free하고 헤더푸터에 f표현 + coalesce함
// chunk size넘어가면? 어떻게해 8000인데 4000만 쓰고있으면?
void mm_free(void *bp)
{
    size_t size = get_size(header_of(bp));
    put(header_of(bp), pack(size, 0));
    put(footer_of(bp), pack(size, 0));
    coalesce(bp);
}

////////////////////////////free_list/////////////////////////////////////
// freelistp를 계속 갱신하면서 앞 뒤만 이음
void make_freesign(void *bp) // free상태인 블럭을 freelist에 삽입
{
    int power = find_power(get_size(header_of(bp)));
    //
    next_freep(bp) = find_freep(power);

    // freelist가 NULL이면 freelist의 처음을 bp로 선언하고 return
    if (find_freep(power) != NULL)
    {
        prev_freep(find_freep(power)) = bp;
    }
    // NULL이 아니면 freelist의 앞에 bp를 삽입
    find_freep(power) = bp;
}

// 있는 freesign 다 지움
void del_freesign(void *bp)
{
    int powerp = find_power(get_size(header_of(bp)));

    // bp가 list의 처음일 때
    if (bp == find_freep(powerp))
    {
        // bp의 다음블럭을 freep의 가장 처음으로 설정
        find_freep(powerp) = next_freep(find_freep(powerp));
        return;
    }
    // list의 처음 아니면 bp의 앞 뒤를 연결함
    ///////////////next가 null이면어 차피 터지는거아님?
    next_freep(prev_freep(bp)) = next_freep(bp);
    if (next_freep(bp) != NULL)
        prev_freep(next_freep(bp)) = prev_freep(bp);
}

int find_power(size_t size)
{
    if (size < 4 * wsize) //
        return -1;

    size_t current_size = 4 * wsize; // 최소크기(16)부터 시작할거
    int i = 0;                       // 리턴할 값 초기화

    while (current_size <= size && i < power_size)
    {
        current_size <<= 1;
        i++; // 비트시프트 한 뒤 power올려줌
    }
    return i;
}

////////////////////////////re-alloc/////////////////////////////////////
// 새 공간에 malloc한 후 데이터를 그쪽으로 옮긴다
void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0) // realloc 하려는 size 0이하면 free
    {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL) // heap 없을때 malloc으로 함
        return mm_malloc(size);

    void *new_bp = mm_malloc(size);

    if (new_bp == NULL) // 힙이 꽉 찼을때
        return 0;

    size_t oldsize = get_size(header_of(bp));

    if (size < oldsize) // size줄어들면 그냥 줄임(데이터는 잘림)
        oldsize = size;

    memcpy(new_bp, bp, oldsize); // 데이터 다른곳에 복사함
    mm_free(bp);                 // 있던 old는 free

    return new_bp;
}

////////////////////////////calloc/////////////////////////////////////
// void *calloc(size_t multiply, size_t size)
// {
//     size_t bytes;
//     void *ptr;
//     // sizeof(x) * multiply만큼 공간 확보 후
//     bytes = multiply * size;
//     ptr = mm_malloc(bytes);
//     memset(ptr, 0, bytes);

//     return ptr;
// } // 짜긴했는데 되는진몰겠네
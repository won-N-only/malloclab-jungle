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

//////////////////////////시스템 개요/////////////////////////////////////
/*
Segregated lists 방식에 First-fit과 Best-fit을 혼용하여 사용.

1. Segregated lists
총 12개의 freelist-master 블럭을 사용.
각 master 블럭은 해당 index 크기 범위 내의 블럭들을 연결리스트로 관리하며 그 범위는 다음과 같음.
{
    index             최저크기        최대크기
     1                  16               31
     2                  32               63
     3                  64              127
     4                 128              255
     5                 256              511
     6                 512             1023
     7                1024             2055
     8                2056             4095
     9                4096             8191
     10               8192            16383
     11              16384            32767
     12              32768            ~~~~~
}

2. find-fit
first와 best 두가지 방식을 둘 다 사용하였음.

index가 작은(크기가 작은)블럭은 first-fit을 이용해 자리를 바로 찾음.
index가 큰(크기가 큰)블럭은 best-fit을 이용해 최대한 단편화가 일어나지 않게 함.

작은 크기의 할당 요청에 신속한 응답을, 큰 크기의 할당 요청에는 높은 메모리 사용 효율을 보장함.

3. realloc
realloc시 앞 뒤 블럭의 가용상태를 확인한 후 collesce함.
realloc시 발생하는 데이터 복사 오버헤드를 줄이고 메모리 단편화를 줄임.
*/

////////////////////////////변수선언/////////////////////////////////////

// 전처리기 매크로 할당
#define wsize 4                           // 워드는 4바이트
#define dsize 8                           // 더블워드는 8바이트
#define max(x, y) ((x) > (y) ? (x) : (y)) // x,y중 max값
#define min(x, y) ((x) < (y) ? (x) : (y)) // x,y중 max값

#define chunksize (1 << 9) // 청크 하나에 512Byte할당

// 크기와 가용여부를 합쳐서(비트연산 활용) 표시함
#define pack(size, alloc) ((size) | (alloc)) // or연산으로 헤더에서 쓸 word만듦

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
#define prev_freep(bp) (*(void **)(bp))         // prev free 블럭으로
#define next_freep(bp) (*(void **)(bp + wsize)) ////next free 블럭으로

// (seglist) 자신의 power에 맞는 가용블럭 찾음
// 크기 2^4면 (heaplistp+wsize*2)만큼 가는식
#define find_master(power) (*(void **)((char *)(heap_listp) + (wsize * (power + 1))))

#define power_size (12) // free list를 (2^4)부터 (2^15 ~ beyond)까지 12개 만들겠다

static char *heap_listp; // 초기 힙 시작 포인터

////////////////////////////함수선언/////////////////////////////////////
int mm_init(void);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void make_freesign(void *bp);
void del_freesign(void *bp);
int find_power(size_t size);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *bp, size_t size);
void *mm_calloc(size_t multiply, size_t size);

////////////////////////////함수시작/////////////////////////////////////
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(16 * wsize)) == (void *)-1)
        return -1;

    put(heap_listp, 0);                                 // 블록 생성 시 패딩
    put(heap_listp + (1 * wsize), pack(14 * wsize, 1)); // 프롤로그 헤더

    char *current_ptr = heap_listp + (2 * wsize); // power의 초기 블록 포인터 설정
    for (int i = 0; i < power_size; i++)          // power_size만큼 블록생성
    {
        put(current_ptr, NULL); // 초기 블록 설정
        current_ptr += wsize;   // 주소 증가시켜 가며 다음 블럭 할당
    }

    put(current_ptr, pack(14 * wsize, 1)); // 프롤로그 푸터
    put(current_ptr + wsize, NULL);        // 에필로그 헤더

    if (extend_heap(chunksize / wsize) == NULL) // 초기 힙 확장
        return -1;

    return 0;
}

// heap 확장
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

////////////////////////////malloc/////////////////////////////////////
void *mm_malloc(size_t size)
{
    size_t asize;       // 블록 사이즈 조정(adjust)
    size_t extend_size; // fit없으면 extend로 넘기기 위한 var
    char *bp;

    if (size == 0)
        return NULL;

    else if (size <= 1 * dsize) // malloc받은 사이즈가 작아서 헤더푸터,prev,next 안들어가면
        asize = 2 * dsize;      // asize에 헤더,푸터,데이터 사이즈(16Byte) 넣음

    else // 무조건 (자기+헤더+푸터) size보다 큰 8의 배수 중 가장 작은값으로 바꿈
        asize = (((size + dsize) + (dsize - 1)) & ~0x7);

    bp = find_fit(asize); // asize 정하고나서 bp에 반영함
    if (bp != NULL)       // fit to asize 찾아서 place
    {
        place(bp, asize);
        return bp;
    }

    // if통과 못하면 size extend하고 다시 place
    extend_size = max(asize, chunksize); // asize와 chunksize중 큰것 찾아서 extend
    if ((bp = extend_heap(extend_size / wsize)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize) // first fit
{
    void *bp;
    int power = find_power(asize); // find power로 asize의 power인덱스 확인
    void *best = NULL;
    if (power >= 6) // asize가 512Byte 이상일때 best fit 시행
    {
        // power선언 되어있으니 재선언 안함
        for (; power <= power_size; power++) // bp를 찾을때까지 power index 순회
        {
            bp = find_master(power); // bp를 power index의 master블럭으로 지정
            while (bp != NULL)       // best 갱신해가면서 끝까지 가고 return
            {
                if (asize <= get_size(header_of(bp)))
                    if (best == NULL || sizeof(header_of(best)) > sizeof(header_of(bp)))
                        best = bp;
                bp = next_freep(bp);
            }
            // 어떤 power index안에서  best 찾았으면 다음 power index 넘어가지 않고 return
            if (best)
                return best;
        }
        return best;
    }
    else // asize가 1024Byte 이하일때 first fit 시행
    {
        // 각 power index 순회하다 크기가 맞는 블럭 나오면 return
        for (; power <= power_size; power++)
        {
            bp = find_master(power);
            while (bp != NULL)
            {
                if (asize <= get_size(header_of(bp)))
                    return bp;
                bp = next_freep(bp);
            }
        }
        return bp;
    }
}

static void place(void *bp, size_t asize) // 찾은 bp에 asize크기로 place
{
    size_t curr_size = get_size(header_of(bp));
    del_freesign(bp);

    if ((curr_size - asize) >= (2 * dsize)) // (블럭 크기) - (asize) 해서 (헤더+푸터 + dsize)보다 크면
    {                                       // 다음블럭에 헤더, 푸터, freesign 넣음
        put(header_of(bp), pack(asize, 1)); // asize만큼 떨어진 헤더 푸터
        put(footer_of(bp), pack(asize, 1)); // 둘다 채우고

        bp = next_block(bp);                            // 다음블럭으로 가서
        put(header_of(bp), pack(curr_size - asize, 0)); // 남은 부분 헤더 푸터 만듦
        put(footer_of(bp), pack(curr_size - asize, 0));

        make_freesign(bp); // freesign 지정
    }
    else // 헤더 푸터 못들어가는 곳이면 다 채움
    {
        put(header_of(bp), pack(curr_size, 1));
        put(footer_of(bp), pack(curr_size, 1));
    }
}

////////////////////////////free/////////////////////////////////////
// free하고 헤더푸터에 free 표현 + coalesce
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

    next_freep(bp) = find_master(power);

    // freelist가 NULL이면 freelist의 처음을 bp로 선언하고 return
    if (find_master(power) != NULL)
    {
        prev_freep(find_master(power)) = bp;
    }
    // NULL이 아니면 freelist의 앞에 bp를 삽입
    find_master(power) = bp;
}

// 있는 freesign 다 지움
void del_freesign(void *bp)
{
    int powerp = find_power(get_size(header_of(bp)));

    // bp가 list의 처음일 때
    if (bp == find_master(powerp))
    {
        // bp의 다음블럭을 freep의 가장 처음으로 설정
        find_master(powerp) = next_freep(find_master(powerp));
        return;
    }
    // list의 처음 아니면 bp의 앞 뒤를 연결함
    next_freep(prev_freep(bp)) = next_freep(bp);

    if (next_freep(bp) != NULL)
        prev_freep(next_freep(bp)) = prev_freep(bp);
}

// 자기 자신의 free 블럭 인덱스를 찾음(2의 i승)
int find_power(size_t size)
{
    size_t current_size = 4 * wsize; // 최소크기(16)부터 시작할거
    int i = 0;                       // 리턴할 값 초기화

    while (current_size <= size && i < power_size) // 자신보다 큰 2의 제곱수를 만났을 때
    {
        current_size <<= 1; // 비트시프트(16 -> 32 -> 64 .....)
        i++;
    }
    return i; // 최소 크기에서 i=1 최대크기에서 i=12
}

////////////////////////////coalesce/////////////////////////////////////
static void *coalesce(void *bp) // 앞 뒤 가용블럭과 free한 블럭 합칩
{
    // 앞 뒤 블럭의 free 여부 확인
    size_t prev_alloc = get_alloc(footer_of(prev_block(bp)));
    size_t next_alloc = get_alloc(header_of(next_block(bp)));
    size_t size = get_size(header_of(bp));

    // 앞 뒤 둘 다 사용중이면 넘어감
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

////////////////////////////re-alloc/////////////////////////////////////
// 새 공간에 malloc한 후 데이터를 그쪽으로 옮김
void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0) // realloc 하려는 size 0이하면 free
    {
        mm_free(bp);
        return NULL;
    }

    if (bp == NULL) // heap 없을때 malloc
        return mm_malloc(size);

    size_t old_size = get_size(header_of(bp));
    size_t new_size = size + (4 * wsize); // 요청한 크기에 header와 footer 추가

    // // 현재 블록의 크기가 충분한 경우 바로 return
    if (new_size < old_size)
        return bp;

    // 다음 가용 블럭의 크기 + 현재 블럭의 크기 >= 요청받은 크기면 coallesce
    if (!get_alloc(header_of(next_block(bp))) && (old_size + get_size(header_of(next_block(bp)))) >= new_size)
    {
        // 내 자리를 그대로 가져가므로 memcpy안하고 진행함
        del_freesign(next_block(bp));
        old_size += get_size(header_of(next_block(bp)));
        put(header_of(bp), pack(old_size, 1));
        put(footer_of(bp), pack(old_size, 1));

        return bp;
    }

    // 이전 블럭의 크기 + 현재 블럭의 크기 >= 요청받은 크기면 coallesce
    else if (!get_alloc(header_of(prev_block(bp))) && (old_size + get_size(header_of(prev_block(bp)))) >= new_size)
    {
        // 이전 블럭으로 옮겨가므로 데이터를 먼저 옮겨줌
        memcpy(prev_block(bp), bp, old_size);

        // 데이터 옮긴 후 coallesce 진행
        bp = prev_block(bp);
        del_freesign(bp);
        old_size += get_size(header_of(bp));
        put(header_of(bp), pack(old_size, 1));
        put(footer_of(bp), pack(old_size, 1));

        return bp;
    }

    // 인접 블록과의 coalesce 불가능할 경우 새로운 공간 할당
    void *new_bp = mm_malloc(size);

    // 기존 데이터 복사
    memcpy(new_bp, bp, size);
    mm_free(bp); // 기존 블록 해제

    return new_bp;
}

//////////////////////////calloc/////////////////////////////////////
void *mm_calloc(size_t multiply, size_t x)
{
    size_t bytes;
    void *ptr;

    // sizeof(x) * multiply만큼 공간 확보 후 0으로 채워서 malloc
    bytes = multiply * x;
    ptr = mm_malloc(bytes);
    memset(ptr, 0, bytes);

    return ptr;
} // 짜긴했는데 되는진몰겠네
#include <iostream>
#include <cstring>
#include <thread>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <atomic>
#include <vector>
#include <cassert>
#include <cstdio>
#define ll long long
#include "sdl_base.h"
using namespace std;
const int ITER = 3;
int GRAPH_TYPE = 0;
int *a;
ll getTicksNs()
{
    static auto startTime = std::chrono::high_resolution_clock::now();
    auto t = std::chrono::high_resolution_clock::now();
    return std::chrono::duration_cast<std::chrono::nanoseconds>(t - startTime).count();
}
struct algorithm
{
    static constexpr int len = 7;
    ll tests[len+1], totalTime[len+1];
    void (*func)(int*, int);
    string name;
    algorithm(string nm, void (*f)(int*, int))
    {
        name = nm;
        func = f;
        fill(tests, tests+len+1, 0);
        fill(totalTime, totalTime+len+1, 0);
    }
    double avg(int pos)
    {
        if(tests[pos] == 0) //no div by 0
            return 0;
        return totalTime[pos] / (double)tests[pos];
    }
    double lavg(int pos)
    {
        if(tests[pos] == 0) //no div by 0
            return 0;
        return log10(totalTime[pos] / (double)tests[pos] + 1);
    }
};
atomic<int> testState;
ll MAX_TIME_LINEAR = 1e8;
void test_sort(algorithm *x, int sz)
{
    int len = pow(10, sz);
    print("sorting " + to_str(len) + " elements with " + x->name);
    flushOutput();
    a = new int[len]; //dynamic memory allocation helps us remove the effects of caching
    for(int i=0; i<len; i++)
        a[i] = randuz();
    ll s = getTicksNs();
    x->func(a, len);
    ll tim = getTicksNs() - s;
    println(": " + to_str(tim/1000000) + "." + to_str(tim%1000000) + "ms");
    flushOutput();
    x->tests[sz]++;
    x->totalTime[sz] += tim;
    MAX_TIME_LINEAR = max(MAX_TIME_LINEAR, (ll)(tim*1.2));
    delete[] a;
    testState = 0;
}
void sort_n(int *a, int n)
{
    sort(a, a+n);
}
int rd = 0;
void custom_qsort_inner(int *a, int *b)
{
    if(a >= b)
        return;
    int *v1 = a, *v2 = (a + (b-a)/2), *v3 = b;
    int *piv;
    if((*v1<*v2) ^ (*v1<*v3))
        piv = v1;
    else if((*v2<*v1) ^ (*v2<*v3))
        piv = v2;
    else piv = v3;
    swap(*a, *piv);
    int *l=a, *r=b;
    l++;
    while(true)
    {
        while(*l<*a)
            l++;
        while(*r>*a)
            r--;
        if(l >= r)
            break;
        swap(*l, *r);
    }
    custom_qsort_inner(a, l-1);
    custom_qsort_inner(l, b);
}
void custom_qsort(int *a, int n)
{
    custom_qsort_inner(a, a+n-1);
    assert(is_sorted(a, a+n));
}
int *v;
void recursive_mergesort(int *a, int n)
{
    if(n == 1)
        return;
    recursive_mergesort(a, n/2);
    recursive_mergesort(a+n/2, (n+1)/2);
    int pos = 0, p1 = 0, p2 = n/2;
    while(p1<n/2 || p2<n)
    {
        if(p1 == n/2)
            v[pos] = a[p2++];
        else if(p2 == n)
            v[pos] = a[p1++];
        else if(a[p1] < a[p2])
            v[pos] = a[p1++];
        else v[pos] = a[p2++];
        pos++;
    }
    for(int i=0; i<n; i++)
        a[i] = v[i];
}
void recursive_mergesort_base(int *a, int n)
{
    v = new int[n];
    recursive_mergesort(a, n);
    delete[] v;
}
void iterative_mergesort(int *a, int n)
{
    v = new int[n];
    for(int i=1; (1<<(i-1))<n; i++)
    {
        for(int j=0; j<n; j+=(1<<i))
        {
            int p2 = j + (1<<(i-1));
            if(p2 >= n)
                break;
            int m = p2, e = min(j+(1<<i), n);
            int p1 = j, pos = 0;
            while(p1<m || p2<e)
            {
                if(p1 == m)
                    v[pos] = a[p2++];
                else if(p2 == e)
                    v[pos] = a[p1++];
                else if(a[p1] < a[p2])
                    v[pos] = a[p1++];
                else v[pos] = a[p2++];
                pos++;
            }
            copy(v, v+pos, a+j);
        }
    }
    delete[] v;
}
void lsd_sort(int *a, int n, int passes, int len)
{
    int *cnt = new int[1<<len], *t = new int[n];
    int MAGIC = (1<<len)-1;
    for(int f=0; f<len*passes; f+=len)
    {
        fill(cnt, cnt+(1<<len), 0);
        for(int i=0; i<n; i++)
            cnt[(a[i] & MAGIC)>>f]++;
        for(int i=1; i<(1<<len); i++)
            cnt[i] += cnt[i-1];
        for(int i=n-1; i>=0; i--)
            t[--cnt[(a[i] & MAGIC)>>f]] = a[i];
        MAGIC <<= len;
        swap(a, t);
    }
    if(passes & 1)
    {
        swap(a, t);
        copy(a, a+n, t);
    }
    delete[] cnt;
    delete[] t;
}
void lsd_sort_2pass(int *a, int n)
{
    lsd_sort(a, n, 2, 14);
}
void lsd_sort_4pass(int *a, int n)
{
    lsd_sort(a, n, 4, 7);
}
void stl_sort_256buckets(int *a, int n)
{
    int *cnt = new int[257], *t = new int[n];
    for(int i=0; i<256; i++)
        cnt[i] = 0;
    cnt[256] = n;
    for(int i=0; i<n; i++)
        cnt[(a[i]>>20)&0xff]++;
    for(int i=1; i<256; i++)
        cnt[i] += cnt[i-1];
    for(int i=0; i<n; i++)
        t[--cnt[(a[i]>>20)&0xff]] = a[i];
    swap(a, t);
    delete[] a;
    for(int i=0; i<256; i++)
        sort(t+cnt[i], t+cnt[i+1]);
    delete[] cnt;
}
int main(int argc, char **argv)
{
    sdl_settings::load_config();
    initSDL("Sorting benchmark");
    thread tester;
    vector<algorithm> algos;
    algos.emplace_back("std::sort", sort_n);
    //algos.emplace_back("quicksort", custom_qsort);
    algos.emplace_back("recursive mergesort", recursive_mergesort_base);
    //algos.emplace_back("iterative mergesort", iterative_mergesort);
    algos.emplace_back("2 pass LSD sort", lsd_sort_2pass);
    algos.emplace_back("4 pass LSD sort", lsd_sort_4pass);
    algos.emplace_back("std::sort with 256 buckets", stl_sort_256buckets);
    int algoPos = -1, lenPos = 1, iterPos = 0;
    int MIN_TEST_LEN = 1;
    while(true)
    {
        if(testState == 0)
        {
            if(algoPos != -1)
                tester.join();
            algoPos++;
            bool done = false;
            if(algoPos == algos.size())
            {
                algoPos = 0;
                lenPos = max(lenPos+1, MIN_TEST_LEN);
                if(lenPos == algorithm::len+1)
                {
                    lenPos = 1;
                    iterPos++;
                    if(iterPos == ITER)
                    {
                        println("done running algorithms");
                        flushOutput();
                        done = true;
                        testState = 2;
                    }
                }
            }
            if(!done)
            {
                testState = 1;
                tester = thread(test_sort, &algos[algoPos], lenPos);
            }
        }
        renderClear(255, 255, 255);
        int cnt = 0;
        int W = sdl_settings::WINDOW_W, H = sdl_settings::WINDOW_H;
        int VOFFSET = H / 20;
        double BLOCK = W / (double)algorithm::len;
        int MAX_TIME_LOG = 11;
        for(auto &i: algos)
        {
            cnt++;
            SDL_Color col{(cnt/4)*200, (cnt/2)*200, (cnt%2)*200};
            fillRect(W/5-H/40, cnt*H/40, H/40, H/40, col.r, col.g, col.b);
            drawText(i.name, W/5, cnt*H/40, H/40);
            setColor(col.r, col.g, col.b);
            switch(GRAPH_TYPE)
            {
            case 0: //log
                for(int j=MIN_TEST_LEN; j<=algorithm::len; j++)
                {
                    fillRect((j-0.5)*BLOCK - H/150, H-i.lavg(j)*H/MAX_TIME_LOG-VOFFSET - H/150, H/75, H/75);
                    if(j != MIN_TEST_LEN)
                        drawLine((j-1.5)*BLOCK, H-i.lavg(j-1)*H/MAX_TIME_LOG-VOFFSET, (j-0.5)*BLOCK, H-i.lavg(j)*H/MAX_TIME_LOG-VOFFSET);
                }
                break;
            case 1: //linear
                for(int j=MIN_TEST_LEN; j<=algorithm::len; j++)
                {
                    fillRect((j-0.5)*BLOCK - H/150, H-i.avg(j)*H/MAX_TIME_LINEAR-VOFFSET - H/150, H/75, H/75);
                    if(j != MIN_TEST_LEN)
                        drawLine((j-1.5)*BLOCK, H-i.avg(j-1)*H/MAX_TIME_LINEAR-VOFFSET, (j-0.5)*BLOCK, H-i.avg(j)*H/MAX_TIME_LINEAR-VOFFSET);
                }
                break;
            }
        }
        setColor(0, 0, 0, 80);
        switch(GRAPH_TYPE)
        {
        case 0:
            for(int i=0; i<MAX_TIME_LOG; i++)
            {
                int V = H-(H*i/MAX_TIME_LOG) - VOFFSET;
                drawLine(0, V, W, V);
                drawText("1e" + to_str(i) + " ns", 0, V-H/40, H/40);
            }
            break;
        case 1:
            for(int i=0; i<MAX_TIME_LOG; i++) //use the same # of intervals
            {
                int V = H-(H*i/MAX_TIME_LOG) - VOFFSET;
                drawLine(0, V, W, V);
                drawText(to_str(i*MAX_TIME_LINEAR/MAX_TIME_LOG) + " ns", 0, V-H/40, H/40);
            }
            break;
        }
        for(int i=1; i<=algorithm::len; i++)
        {
            drawText("1e" + to_str(i), (i-0.5)*BLOCK - 3*H/160, H-VOFFSET, H/40);
        }
        updateScreen();
        while(SDL_PollEvent(&input))
        {
            switch(input.type)
            {
            case SDL_QUIT:
                sdl_settings::output_config();
                SDL_Quit();
                if(testState != 2)
                    tester.join();
                return 0;
            case SDL_KEYDOWN:
                switch(input.key.keysym.sym)
                {
                case SDLK_g:
                    GRAPH_TYPE++;
                    GRAPH_TYPE %= 2;
                    break;
                }
                break;
            }
        }
    }
    return 0;
}

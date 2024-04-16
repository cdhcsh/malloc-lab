#include "mm.h"
#include "memlib.h"
#include <stdio.h>

int _get_class(size_t size)
{
    int class = -4;
    while (size > 0 && class < 12)
    {
        class += 1;
        size >>= 1;
    }
    return class - 1 > 0 ? class - 1 : 0;
}
int main(void)
{
    printf("%d\n", _get_class(63));
    return 0;
}

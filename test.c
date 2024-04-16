// #include "mm.h"
// #include "memlib.h"
#include <stdio.h>

#define GET_BLOCK_SIZE(class) (1 << (5 + class))

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
    int class = _get_class(65);
    printf("%d\n", class);
    printf("%d\n", GET_BLOCK_SIZE(class));

    return 0;
}

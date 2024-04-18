// #include "mm.h"
// #include "memlib.h"
#include <stdio.h>

#define GET_BLOCK_SIZE(class) (1 << (4 + class))

int _get_class(size_t size)
{
    size -= 1;
    int class = -3;
    while (size > 0 && class < 12)
    {
        class += 1;
        size >>= 1;
    }
    return class - 1 > 0 ? class - 1 : 0;
}
int main(void)
{
    int class = _get_class(53);
    printf("%d\n", class);
    printf("%d\n", GET_BLOCK_SIZE(class));

    return 0;
}

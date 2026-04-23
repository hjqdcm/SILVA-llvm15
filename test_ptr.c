#include <stdlib.h>
#include <stdio.h>

int inc(int *p) {
    if (!p) return -1;
    *p += 1;
    return *p;
}

int main(void) {
    int *x = (int *)malloc(sizeof(int));
    if (!x) return 1;
    *x = 41;

    // Force a pointer cast through void* to exercise getPtrElementType logic.
    void *tmp = x;
    int *y = (int *)tmp;

    int result = inc(y);
    free(x);
    return result;
}

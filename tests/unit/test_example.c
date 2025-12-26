#include <stdarg.h>
#include <stddef.h>
#include <setjmp.h>
#include <stdint.h>
#include <cmocka.h>

#include "gate_example.h"

/* Test function for example_function */
static void test_example_function(void **state) {
    /* The function should return 0 on success */
    assert_int_equal(example_function(), 0);
}

/* Main entry point for the test */
int main(void) {
    const struct CMUnitTest tests[] = {
        cmocka_unit_test(test_example_function),
    };
    
    return cmocka_run_group_tests(tests, NULL, NULL);
}
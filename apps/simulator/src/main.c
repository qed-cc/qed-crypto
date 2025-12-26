#include <stdio.h>
#include "gate_example.h"  /* Include from gate_example module */

/**
 * @brief Main entry point for the simulator application
 * @param argc Argument count
 * @param argv Argument values
 * @return Status code
 */
int main(int argc, char *argv[]) {
    printf("Gate Computer Simulator\n");
    
    /* Use example module functionality */
    int result = example_function();
    
    printf("Example function returned: %d\n", result);
    
    return 0;
}
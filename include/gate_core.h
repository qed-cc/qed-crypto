#ifndef GATE_CORE_H
#define GATE_CORE_H

/**
 * @file gate_core.h
 * @brief Core functionality for the Gate Computer
 */

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Initialize the gate computer core
 * @return 0 on success
 */
int gate_core_init(void);

/**
 * @brief Cleanup the gate computer core
 * @return 0 on success
 */
int gate_core_cleanup(void);

#ifdef __cplusplus
}
#endif

#endif /* GATE_CORE_H */
#ifndef SAIL_COVERAGE_H
#define SAIL_COVERAGE_H

int sail_coverage_exit(void);

void sail_function_entry(char *function_name, char *sail_file, int l1, int c1, int l2, int c2);

void sail_branch_taken(int branch_id, char *sail_file, int l1, int c1, int l2, int c2);

void sail_branch_reached(int branch_id, char *sail_file, int l1, int c1, int l2, int c2);

#endif

#include <sail_failure.h>

#include <stdio.h>
#include <stdlib.h>

void sail_match_failure(char *message)
{
     fprintf(stderr, "Match failure: %s", message);
     exit(EXIT_FAILURE);
}

void sail_failure(char *message)
{
     fprintf(stderr, "Failure: %s", message);
     exit(EXIT_FAILURE);
}

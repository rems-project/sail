#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

for i in `ls $DIR/pass/`;
do
  printf "testing $i expecting pass: "
  if $DIR/../../sail $1 $DIR/pass/$i 2> /dev/null;
  then
    printf "${GREEN}pass${NC}\n"
  else
    printf "${RED}fail${NC}\n"
  fi
done

for i in `ls $DIR/fail/`;
do
  printf "testing $i expecting fail: "
  if $DIR/../../sail $1 $DIR/fail/$i 2> /dev/null;
  then
    printf "${RED}pass${NC}\n"
  else
    printf "${GREEN}fail${NC}\n"
  fi
done

for i in `ls $DIR/nice/`;
do
  printf "testing $i would like pass: "
  if $DIR/../../sail $1 $DIR/nice/$i 2> /dev/null;
  then
    printf "${GREEN}pass${NC}\n"
  else
    printf "${YELLOW}fail${NC}\n"
  fi
done

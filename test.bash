#! /bin/bash

make clean
agda $1
agda2atp $1

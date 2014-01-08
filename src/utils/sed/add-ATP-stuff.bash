#! /bin/bash

find -name '*.agda' -execdir sed -i 's/-- {-# ATP/{-# ATP/g' '{}' ';'

find -name '*.agda' \
     -execdir sed -i 's/-- {-# OPTIONS --schematic/{-# OPTIONS --schematic/' \
              '{}' ';'

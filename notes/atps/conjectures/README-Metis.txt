From
http://www.gilith.com/pipermail/metis-users/2010-September/000001.html,
Metis could continue running even if we use the --time-limit
option. Therefore, to test Metis in the conjectures it is necessary to
use

$ ulimit -S -t 180
$ make make only_conjectures_FOTC
$ ulimit -S -t unlimited

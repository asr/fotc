* Metis might continue to run past the time limit, so for testing with
  Metis we should use the following commands:

$ ulimit -S -t 240
$ run test
$ ulimit -S -t unlimited

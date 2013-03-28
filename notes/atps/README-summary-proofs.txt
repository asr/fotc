* Metis might continue to run past the time limit, so for testing with
  Metis we should use the following commands:

$ ulimit -S -t xxx
$ run test
$ ulimit -S -t unlimited

where xxx is the value of --time + 10%.

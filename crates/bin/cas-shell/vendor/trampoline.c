/*
** Makes the vendored SQLite shell survivable inside a host process.
**
** `shell.c` is a program, and programs terminate by calling `exit()`. Upstream
** funnels most of those through `cli_exit()`, but not all of them: argument
** parsing and a few fatal paths call `exit()` directly. Embedding the shell
** unchanged therefore means an unopenable database takes the whole host down
** with it, which is unacceptable for a REPL that intends to return to its own
** prompt.
**
** Rather than patch the vendored source, the build compiles `shell.c` with
** `-Dexit=covalence_shell_exit`. That is a whole-token replacement across the
** translation unit, so it captures `cli_exit`'s call and every direct call at
** once, and `<stdlib.h>` conveniently supplies the prototype. This file
** provides the replacement and the `setjmp` landing pad it returns to.
**
** The cost is honest and bounded: a shell which exits this way leaks whatever
** it had allocated, because nothing unwinds. That is acceptable for a
** debugging surface which is outside the trusted computing base, and it is
** strictly better than terminating the process. It is not acceptable for
** anything on which a correctness claim depends, and nothing is.
*/

#include <limits.h>
#include <setjmp.h>
#include <stdlib.h>

/* `shell.c`'s `main`, renamed by the build script. */
int covalence_sqlite_shell_main(int argc, char **argv);

static jmp_buf covalence_shell_landing_pad;

/* Non-zero only while a shell invocation is on the stack below the pad. */
static int covalence_shell_running = 0;

/*
** `longjmp` treats 0 as 1, so a genuine exit status of 0 needs a distinct
** value to travel under. `INT_MIN` is not a possible process exit status.
*/
#define COVALENCE_SHELL_EXIT_ZERO INT_MIN

_Noreturn void covalence_shell_exit(int status){
  if( covalence_shell_running ){
    longjmp(covalence_shell_landing_pad,
            status==0 ? COVALENCE_SHELL_EXIT_ZERO : status);
  }
  /* Nothing to return to. Terminating is the honest outcome. */
  _Exit(status);
}

/*
** Runs the shell and returns its exit status, whether it returned normally or
** tried to terminate the process.
*/
int covalence_sqlite_shell_run(int argc, char **argv){
  int status = setjmp(covalence_shell_landing_pad);
  if( status!=0 ){
    covalence_shell_running = 0;
    return status==COVALENCE_SHELL_EXIT_ZERO ? 0 : status;
  }
  covalence_shell_running = 1;
  status = covalence_sqlite_shell_main(argc, argv);
  covalence_shell_running = 0;
  return status;
}

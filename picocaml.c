/*
 * OCaml bindings for picosat 936
 *
 *   * compile with e.g. 
 *       $ gcc -I<PathToOcamlHeaders> -I <PathToPicosat> -c picocaml.c
 *   * to build an interactive interpreter supporting picosat queries issue
 *       $ ocamlmktop -custom -o picocaml picocaml.o \
 *         <PathToPicosat>/picosat.o <PathToPicosat>/version.o picocaml.ml
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <stdarg.h>

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

#include <picosat.h>

/* Declarations */
static int out(FILE *f, char *fmt, ...); 

/* Types */
typedef struct cls { int *lits; } cls;
typedef cls * cblk;

/* Macros, Constants, ... */
#define BLK_S 1024 /* size of clause blocks */
#define CLS_S 256  /* initial size of clause buffer */

/* Globals */
static cblk *cbuf=NULL;
static unsigned int sccbuf=0;
static unsigned int lccbuf=0;
static int *clbuf=NULL;
static unsigned int sclbuf=0;
static unsigned int fclbuf=0;
static unsigned int lastrv=0;
static unsigned char initialized=0; /* 0: uninitialized, !=0: initialized */
static unsigned char tr_enabled=0;  /* 0: no traces, !=0: traces enabled */
static int last_res=PICOSAT_UNKNOWN;

/* 
 * Function definitions
 */

void ck_clbuf() {
  if (clbuf==NULL && sclbuf==0) { 
    clbuf=(int *)malloc(CLS_S*sizeof(int));
    sclbuf=CLS_S;
  }
  assert(clbuf);
}

void rsz_clbuf() {
  ck_clbuf();
  if (fclbuf>=sclbuf) {
    int *new=realloc(clbuf, sclbuf*2*sizeof(int));
    assert(new);
    clbuf=new;
    sclbuf*=2;
  }
}

void psh_clbuf(int i) {
  ck_clbuf();
  if (fclbuf<sclbuf)
    clbuf[fclbuf++]=i;
  else {
    rsz_clbuf();
    psh_clbuf(i);
  }
}

void print_clbuf() {
  int i=0;
  unsigned char fst=1;

  putchar('[');
  while (i<fclbuf) {
    printf("%s%d", fst==1 ? "" : ", ", clbuf[i++]);
    if (fst)
      fst=0;
  }
  puts("]");
  fflush(stdout);
}

void cl_clbuf() {
  fclbuf=0;
}

void ck_cbuf() {
  if (cbuf==NULL && sccbuf==0) {
    cbuf=(cblk*)malloc(BLK_S*sizeof(cblk));
    sccbuf=BLK_S;
  }
  assert(cbuf);
}

void rsz_cbuf() {
  ck_cbuf();
  if (lccbuf>=sccbuf) {
    cblk *n=NULL;
    while (sccbuf<=lccbuf)
      sccbuf+=BLK_S;
    n=realloc(cbuf, sccbuf);
    assert(n);
    cbuf=n;
  }
}

void psh_cbuf(cls *c) {
  ck_cbuf();
  if (lccbuf<sccbuf)
    cbuf[lccbuf++]=c;
  else {
    rsz_cbuf();
    psh_cbuf(c);
  }
}

cls *new_cls() {
  cls *rv=(cls *)malloc(sizeof(cls));
  assert(rv);
  rv->lits=(int *)malloc((fclbuf+1)*sizeof(int));
  assert(rv->lits);
  memcpy(rv->lits, clbuf, fclbuf*sizeof(int));
  rv->lits[fclbuf]=0;

  return rv;
}

void del_cls(cls *c) {
  free(c->lits);
  free(c);
}

/* call this one when resetting the solver */
void tear_down() {
  int i=0;

  /* delete all clauses */
  for (; i<lccbuf; i++)
    del_cls(cbuf[i]);
  free(cbuf);
  cbuf=NULL;

  /* clear clause buffer */
  free(clbuf);
  clbuf=NULL;

  /* clear all length & size counters */
  lccbuf=0;
  sccbuf=0;
  sclbuf=0;
  fclbuf=0;
}

int add_picosat(cls *c) {
  int i=0;
  assert(c);
  while (c->lits[i])
    picosat_add(c->lits[i++]);

  return picosat_add(0);
}

/* add_clause: int list -> unit */
value add_cls(value ls) {
  CAMLparam1(ls);
  CAMLlocal1(p);
  cls *c=NULL;

  if (!initialized) {
    out(stderr, "Solver not yet initialized, no clause added!\n");
    CAMLreturn(Val_unit);
  }

  p=ls;
  cl_clbuf();
  while (p!=Val_int(0)) {
    psh_clbuf(Int_val(Field(p, 0)));
    p=Field(p,1);
  }
  print_clbuf();
  c=new_cls();
  assert(add_picosat(c)==lccbuf);
  psh_cbuf(c);
  cl_clbuf();

  CAMLreturn(Val_unit);
}

/* add_clauses: int list list -> unit */
value add_clss(value ls) {
  CAMLparam1(ls);
  CAMLlocal1(p);

  if (!initialized) {
    out(stderr, "Solver not yet initialized, no clauses added!\n");
    CAMLreturn(Val_unit);
  }

  p = ls;
  while (p!=Val_int(0)) {
    add_cls(Field(p, 0));
    p=Field(p, 1);
  }

  CAMLreturn(Val_unit);
}

value cons(value v1, value v2) {
  CAMLparam2(v1, v2);
  CAMLlocal1(rv);
  
  rv = caml_alloc(2,0);
  Store_field(rv, 0, v1);
  Store_field(rv, 1, v2);

  CAMLreturn(rv);
}

/* get_clauses: unit -> int list list */
value get_clauses(value unit) {
  CAMLparam1(unit);
  CAMLlocal2(rv,acc);
  int i=lccbuf-1;

  rv=Val_emptylist;
  while (i>=0) {
    cls *c=cbuf[i--];
    int j=0;

    acc=Val_emptylist;
    while (c->lits[j])
      acc=cons(Val_int(c->lits[j++]), acc);
    rv=cons(acc, rv);
  }

  CAMLreturn(rv);
}

value ps_unsat_core(value clauselim) {
  CAMLparam1(clauselim);
  CAMLlocal2(rv, acc);
  int i=Int_val(clauselim);

  if (i<0 || i>=lccbuf)
    i=lccbuf-1;
  rv=Val_emptylist;
  if (!initialized) {
    out(stderr, "Solver not yet initialized, no unsat core available!\n");
    CAMLreturn(rv);
  }

  if (last_res==PICOSAT_UNSATISFIABLE) {
    while (i>=0) {
      if (picosat_coreclause(i)) {
        int j=0;
        cls *c=cbuf[i];

        acc=Val_emptylist;
        while (c->lits[j])
          acc=cons(Val_int(c->lits[j++]), acc);
        rv=cons(acc, rv);
      }
      i--;
    }
  }

  CAMLreturn(rv);
}

value ps_get_model(value unit) {
  CAMLparam1(unit);
  CAMLlocal1(rv);

  rv=Val_emptylist;
  if (!initialized) {
    out(stderr, "Solver not yet initialized, no model available!\n");
    CAMLreturn(rv);
  }

  if (last_res==PICOSAT_SATISFIABLE) {
    int i=1, lit=0;
    for (; i<=picosat_variables(); i++)
      if ((lit=i*picosat_deref(i))!=0)
        rv=cons(Val_int(lit), rv);
  }

  CAMLreturn(rv);
}

value ps_init(value unit) {
  CAMLparam1(unit);

  if (initialized) {
    out(stderr, "Solver already initialized!\n");

    CAMLreturn(Val_unit);
  }
  initialized=1;
  picosat_init();

  if (!(tr_enabled=picosat_enable_trace_generation()))
    out(stderr, "Solver doesn't support trace generation!\n");
  else
    out(stdout, "Solver with trace generation support prepared.\n");

  CAMLreturn(Val_unit);
}

value ps_reset(value unit) {
  CAMLparam1(unit);

  if (!initialized) {
    out(stderr, "Solver not initialized, couldn't reset it!\n");
    CAMLreturn(Val_unit);
  }
  tear_down();
  initialized=0;
  tr_enabled=0;
  last_res=PICOSAT_UNKNOWN;
  picosat_reset();

  CAMLreturn(Val_unit);
}

value ps_sat(value timeout) {
  CAMLparam1(timeout);

  if (!initialized) {
    out(stderr, "Solver not initialized, couldn't check satisfiability!\n");
    CAMLreturn(Val_int(PICOSAT_UNKNOWN));
  }
  last_res=picosat_sat(Int_val(timeout));

  CAMLreturn(Val_int(last_res));
}


static int out(FILE *f, char *fmt, ...) {
  int rv;
  va_list ap;

  va_start(ap, fmt);
  rv=vfprintf(f, fmt, ap);
  fflush(f);
  va_end(ap);

  return rv;
}

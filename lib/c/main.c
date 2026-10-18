// SPDX-License-Identifier: CC0-1.0
//
// Command line front end for the C port of `decideHamPath` (fast mode), same input formats, flags,
// output and exit codes as lib/python/hpst_cli.py (see lib/README.md):
//
//   hpst [FILE] [--mode fast] [--draw] [--json] [--check] [--stats] [--no-heuristic]
//
// Exit codes: 0 answered (yes or no), 1 --check disagreement or invalid witness,
// 2 bad input (format, missing endpoints, non-solid V) or bad arguments.
//
#define _POSIX_C_SOURCE 199309L

#include <errno.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "hpst.h"

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ((double)ts.tv_sec) + (1e-9 * ((double)ts.tv_nsec));
}

static void *xmalloc(size_t n) {
  void *p = malloc( (n == 0) ? 1 : n );
  if (!p) { fprintf(stderr, "hpst: out of memory\n"); exit(2); }
  return p;
}

static void *xrealloc(void *p, size_t n) {
  p = realloc(p, (n == 0) ? 1 : n);
  if (!p) { fprintf(stderr, "hpst: out of memory\n"); exit(2); }
  return p;
}

static char g_err[512];

// ---------------------------------------------------------------------------------------------
// Point sets.
// ---------------------------------------------------------------------------------------------

typedef struct {
  hpst_pt *v;
  int      n, cap;
} PtVec;

static void pv_add(PtVec *a, int x, int y) {
  if (a->n >= a->cap) {
    a->cap = (2 * a->cap) + 64;
    a->v   = xrealloc(a->v, ((size_t)a->cap) * sizeof(hpst_pt));
  }
  a->v[a->n].x = x;
  a->v[a->n].y = y;
  a->n++;
}

static int cmp_pt(const void *a, const void *b) {
  const hpst_pt *p = a, *q = b;
  if (p->x != q->x) { return ( (p->x < q->x) ? -1 : 1 ); }
  if (p->y != q->y) { return ( (p->y < q->y) ? -1 : 1 ); }
  return 0;
}

// Sort and remove duplicates (V is a set in Python).
//
static void pv_unique(PtVec *a) {
  int i, m = 0;
  qsort(a->v, (size_t)a->n, sizeof(hpst_pt), cmp_pt);
  for (i = 0; i < a->n; i++) {
    if ( (m == 0) || (cmp_pt(&a->v[m - 1], &a->v[i]) != 0) ) { a->v[m++] = a->v[i]; }
  }
  a->n = m;
}

static int pv_has(const PtVec *a, hpst_pt p) {
  return ( bsearch(&p, a->v, (size_t)a->n, sizeof(hpst_pt), cmp_pt) != NULL );
}

// ---------------------------------------------------------------------------------------------
// ASCII grid input: one line per row, top row first. `.` point, `#` / space / tab not a point,
// `s` / `t` the endpoints; `;` comment lines; blank lines before the first and after the last
// grid line ignored. x = column, y = row counted from the bottom.
// ---------------------------------------------------------------------------------------------

static int is_blank(const char *a, const char *b) {
  for (; a < b; a++) {
    if ( (*a != ' ') && (*a != '\t') && (*a != '\r') && (*a != '\n') && (*a != '\v') &&
         (*a != '\f') ) {
      return 0;
    }
  }
  return 1;
}

static int parse_ascii(char *text, PtVec *V, int *hs, hpst_pt *s, int *ht, hpst_pt *t) {
  int nl = 0, cap = 0, i, r0, r1, h;
  char **ls = NULL, **le = NULL, *p = text;

  // Split on '\n'; strip trailing '\r'; drop comment lines.
  //
  for (;;) {
    char *q = strchr(p, '\n'), *e = ( q ? q : (p + strlen(p)) );
    char *b = e;
    while ( (b > p) && (b[-1] == '\r') ) { b--; }
    if (*p != ';') {
      if (nl >= cap) {
        cap = (2 * cap) + 64;
        ls  = xrealloc(ls, ((size_t)cap) * sizeof(char *));
        le  = xrealloc(le, ((size_t)cap) * sizeof(char *));
      }
      ls[nl] = p;
      le[nl] = b;
      nl++;
    }
    if (!q) { break; }
    p = q + 1;
  }
  r0 = 0;
  r1 = nl;
  while ( (r0 < r1) && is_blank(ls[r0], le[r0]) )         { r0++; }
  while ( (r1 > r0) && is_blank(ls[r1 - 1], le[r1 - 1]) ) { r1--; }
  if (r0 >= r1) {
    snprintf(g_err, sizeof(g_err), "empty grid");
    free(ls); free(le);
    return 0;
  }
  h = r1 - r0;
  for (i = r0; i < r1; i++) {
    int r = i - r0, y = h - 1 - r, x = 0;
    const char *c;
    for (c = ls[i]; c < le[i]; c++, x++) {
      unsigned char ch = (unsigned char)*c;
      if ( (ch == '.') || (ch == 's') || (ch == 't') ) {
        pv_add(V, x, y);
        if (ch == 's') {
          if (*hs) {
            snprintf(g_err, sizeof(g_err), "more than one 's'");
            free(ls); free(le);
            return 0;
          }
          *hs = 1; s->x = x; s->y = y;
        }
        else if (ch == 't') {
          if (*ht) {
            snprintf(g_err, sizeof(g_err), "more than one 't'");
            free(ls); free(le);
            return 0;
          }
          *ht = 1; t->x = x; t->y = y;
        }
      }
      else if ( (ch != '#') && (ch != ' ') && (ch != '\t') ) {
        if ( (ch >= 32) && (ch < 127) ) {
          snprintf(g_err, sizeof(g_err), "unexpected character '%c' at row %d column %d", ch,
                   r + 1, x);
        }
        else {
          snprintf(g_err, sizeof(g_err), "unexpected character '\\x%02x' at row %d column %d",
                   ch, r + 1, x);
        }
        free(ls); free(le);
        return 0;
      }
    }
  }
  free(ls); free(le);
  return 1;
}

// ---------------------------------------------------------------------------------------------
// JSON input: {"points": [[x, y], ...], "s": [x, y], "t": [x, y]}. A small recursive-descent
// parser for the whole JSON grammar; only the three keys are used.
// ---------------------------------------------------------------------------------------------

enum { J_NULL, J_BOOL, J_NUM, J_STR, J_ARR, J_OBJ };

typedef struct JV {
  int          type;
  double       num;
  char        *str;
  int          n;
  struct JV  **items;
  char       **keys;
} JV;

typedef struct {
  const char *p;
  const char *err;
  int         depth;
} JP;

static void jfree(JV *v) {
  int i;
  if (!v) { return; }
  for (i = 0; i < v->n; i++) {
    jfree(v->items[i]);
    if (v->keys) { free(v->keys[i]); }
  }
  free(v->items);
  free(v->keys);
  free(v->str);
  free(v);
}

static void jws(JP *j) {
  while ( (*j->p == ' ') || (*j->p == '\t') || (*j->p == '\n') || (*j->p == '\r') ) { j->p++; }
}

static JV *jnew(int type) {
  JV *v = xmalloc(sizeof(JV));
  memset(v, 0, sizeof(JV));
  v->type = type;
  return v;
}

static JV *jvalue(JP *j);

static char *jstring(JP *j) {
  size_t cap = 16, n = 0;
  char *out = xmalloc(cap);
  j->p++;
  for (;;) {
    char c = *j->p;
    if (c == 0) {
      j->err = "unterminated string";
      free(out);
      return NULL;
    }
    j->p++;
    if (c == '"') { break; }
    if (c == '\\') {
      char d = *j->p;
      if (d == 0) {
        j->err = "bad escape";
        free(out);
        return NULL;
      }
      j->p++;
      if (d == 'u') {
        int k;
        for (k = 0; k < 4; k++) {
          if (!( ((j->p[k] >= '0') && (j->p[k] <= '9')) || ((j->p[k] >= 'a') && (j->p[k] <= 'f')) ||
                 ((j->p[k] >= 'A') && (j->p[k] <= 'F')) )) {
            j->err = "bad \\u escape";
            free(out);
            return NULL;
          }
        }
        j->p += 4;
        c = '?';
      }
      else if (d == 'n') { c = '\n'; }
      else if (d == 't') { c = '\t'; }
      else if (d == 'r') { c = '\r'; }
      else if (d == 'b') { c = '\b'; }
      else if (d == 'f') { c = '\f'; }
      else if ( (d == '"') || (d == '\\') || (d == '/') ) { c = d; }
      else {
        j->err = "bad escape";
        free(out);
        return NULL;
      }
    }
    if ((n + 2) > cap) {
      cap *= 2;
      out  = xrealloc(out, cap);
    }
    out[n++] = c;
  }
  out[n] = 0;
  return out;
}

static JV *jvalue(JP *j) {
  JV *v;
  jws(j);
  if (++j->depth > 1000) {
    j->err = "nesting too deep";
    return NULL;
  }
  if (*j->p == '{') {
    v = jnew(J_OBJ);
    j->p++;
    jws(j);
    if (*j->p == '}') {
      j->p++;
      j->depth--;
      return v;
    }
    for (;;) {
      char *k;
      JV *x;
      jws(j);
      if (*j->p != '"') {
        j->err = "expecting property name";
        jfree(v);
        return NULL;
      }
      k = jstring(j);
      if (!k) {
        jfree(v);
        return NULL;
      }
      jws(j);
      if (*j->p != ':') {
        j->err = "expecting ':'";
        free(k);
        jfree(v);
        return NULL;
      }
      j->p++;
      x = jvalue(j);
      if (!x) {
        free(k);
        jfree(v);
        return NULL;
      }
      v->items = xrealloc(v->items, ((size_t)v->n + 1) * sizeof(JV *));
      v->keys  = xrealloc(v->keys, ((size_t)v->n + 1) * sizeof(char *));
      v->items[v->n] = x;
      v->keys[v->n]  = k;
      v->n++;
      jws(j);
      if (*j->p == ',') {
        j->p++;
        continue;
      }
      if (*j->p == '}') {
        j->p++;
        break;
      }
      j->err = "expecting ',' or '}'";
      jfree(v);
      return NULL;
    }
  }
  else if (*j->p == '[') {
    v = jnew(J_ARR);
    j->p++;
    jws(j);
    if (*j->p == ']') {
      j->p++;
      j->depth--;
      return v;
    }
    for (;;) {
      JV *x = jvalue(j);
      if (!x) {
        jfree(v);
        return NULL;
      }
      v->items = xrealloc(v->items, ((size_t)v->n + 1) * sizeof(JV *));
      v->items[v->n++] = x;
      jws(j);
      if (*j->p == ',') {
        j->p++;
        continue;
      }
      if (*j->p == ']') {
        j->p++;
        break;
      }
      j->err = "expecting ',' or ']'";
      jfree(v);
      return NULL;
    }
  }
  else if (*j->p == '"') {
    char *s = jstring(j);
    if (!s) { return NULL; }
    v = jnew(J_STR);
    v->str = s;
  }
  else if (strncmp(j->p, "true", 4) == 0)  { v = jnew(J_BOOL); v->num = 1; j->p += 4; }
  else if (strncmp(j->p, "false", 5) == 0) { v = jnew(J_BOOL); v->num = 0; j->p += 5; }
  else if (strncmp(j->p, "null", 4) == 0)  { v = jnew(J_NULL); j->p += 4; }
  else if ( (*j->p == '-') || ((*j->p >= '0') && (*j->p <= '9')) ) {
    char *e;
    double d = strtod(j->p, &e);
    if (e == j->p) {
      j->err = "bad number";
      return NULL;
    }
    v = jnew(J_NUM);
    v->num = d;
    j->p = e;
  }
  else {
    j->err = "expecting value";
    return NULL;
  }
  j->depth--;
  return v;
}

static JV *jget(const JV *o, const char *k) {
  int i;
  JV *r = NULL;
  for (i = 0; i < o->n; i++) {
    if (strcmp(o->keys[i], k) == 0) { r = o->items[i]; }
  }
  return r;
}

// Python int() of a JSON number or bool (truncation toward zero).
//
static int jint(const JV *v, int *out) {
  if ( (!v) || ( (v->type != J_NUM) && (v->type != J_BOOL) ) ) { return 0; }
  if ( (!isfinite(v->num)) || (fabs(v->num) > 1e9) ) { return 0; }
  *out = (int)v->num;
  return 1;
}

// An endpoint: absent or null -> *has = 0; an array of 2 numbers -> the point; an array of
// another length -> *has = 2 (Python makes a tuple that is not a point of V).
//
static int jpoint(const JV *v, int *has, hpst_pt *p) {
  int i, c[2];
  if ( (!v) || (v->type == J_NULL) ) {
    *has = 0;
    return 1;
  }
  if ( (v->type != J_ARR) && (v->type != J_STR) ) { return 0; }
  if (v->type == J_STR) { return 0; }
  for (i = 0; i < v->n; i++) {
    int dummy;
    if (!jint(v->items[i], &dummy)) { return 0; }
  }
  if (v->n != 2) {
    *has = 2;
    return 1;
  }
  jint(v->items[0], &c[0]);
  jint(v->items[1], &c[1]);
  p->x = c[0];
  p->y = c[1];
  *has = 1;
  return 1;
}

static int parse_json(const char *text, PtVec *V, int *hs, hpst_pt *s, int *ht, hpst_pt *t) {
  JP j;
  JV *root, *pts;
  int i, ok = 1;
  j.p = text; j.err = NULL; j.depth = 0;
  root = jvalue(&j);
  if (root) {
    jws(&j);
    if (*j.p != 0) {
      j.err = "extra data";
      jfree(root);
      root = NULL;
    }
  }
  if (!root) {
    snprintf(g_err, sizeof(g_err), "bad JSON input: %s at char %ld", j.err,
             (long)(j.p - text));
    return 0;
  }
  if (root->type != J_OBJ) {
    snprintf(g_err, sizeof(g_err), "bad JSON input: not an object");
    jfree(root);
    return 0;
  }
  pts = jget(root, "points");
  if ( (!pts) || (pts->type != J_ARR) ) {
    snprintf(g_err, sizeof(g_err), "bad JSON input: 'points' missing or not a list");
    jfree(root);
    return 0;
  }
  for (i = 0; ( ok && (i < pts->n) ); i++) {
    JV *q = pts->items[i];
    int x, y;
    if ( (q->type != J_ARR) || (q->n < 2) || (!jint(q->items[0], &x)) ||
         (!jint(q->items[1], &y)) ) {
      ok = 0;
      break;
    }
    pv_add(V, x, y);
  }
  if (!ok) {
    snprintf(g_err, sizeof(g_err), "bad JSON input: point %d is not [x, y]", i);
    jfree(root);
    return 0;
  }
  if ( (!jpoint(jget(root, "s"), hs, s)) || (!jpoint(jget(root, "t"), ht, t)) ) {
    snprintf(g_err, sizeof(g_err), "bad JSON input: endpoint is not [x, y]");
    jfree(root);
    return 0;
  }
  jfree(root);
  return 1;
}

// ---------------------------------------------------------------------------------------------
// Output helpers: UTF-8 drawing, JSON strings, Python float repr of round(x, 4).
// ---------------------------------------------------------------------------------------------

typedef struct {
  char  *b;
  size_t n, cap;
} Buf;

static void bput(Buf *o, const char *s, size_t k) {
  if ((o->n + k + 1) > o->cap) {
    o->cap = (2 * o->cap) + k + 64;
    o->b   = xrealloc(o->b, o->cap);
  }
  memcpy(o->b + o->n, s, k);
  o->n += k;
  o->b[o->n] = 0;
}

static void bputs(Buf *o, const char *s) { bput(o, s, strlen(s)); }

static void bcp(Buf *o, int cp) {
  char u[4];
  if (cp < 0x80) {
    u[0] = (char)cp;
    bput(o, u, 1);
  }
  else {
    u[0] = (char)(0xe0 | (cp >> 12));
    u[1] = (char)(0x80 | ((cp >> 6) & 0x3f));
    u[2] = (char)(0x80 | (cp & 0x3f));
    bput(o, u, 3);
  }
}

// Box characters: points on even columns and rows, path edges between them (hpst_cli.draw).
//
static char *draw(const PtVec *V, hpst_pt s, hpst_pt t, const hpst_pt *P, int np) {
  int x0, x1, y0, y1, W, Hh, i, x, y, *cps, ncp;
  unsigned char *in, *cn;
  Buf o = { NULL, 0, 0 };
  x0 = x1 = V->v[0].x;
  y0 = y1 = V->v[0].y;
  for (i = 0; i < V->n; i++) {
    if (V->v[i].x < x0) { x0 = V->v[i].x; }
    if (V->v[i].x > x1) { x1 = V->v[i].x; }
    if (V->v[i].y < y0) { y0 = V->v[i].y; }
    if (V->v[i].y > y1) { y1 = V->v[i].y; }
  }
  W  = x1 - x0 + 1;
  Hh = y1 - y0 + 1;
  in = calloc((size_t)W * (size_t)Hh, 1);
  cn = calloc((size_t)W * (size_t)Hh, 1);
  if ( (!in) || (!cn) ) { fprintf(stderr, "hpst: out of memory\n"); exit(2); }
  for (i = 0; i < V->n; i++) { in[(V->v[i].x - x0) + ((V->v[i].y - y0) * W)] = 1; }

  // Connection bits per point: 1 right, 2 left, 4 up, 8 down.
  //
  for (i = 0; ( P && (i + 1 < np) ); i++) {
    hpst_pt a = P[i], b = P[i + 1];
    int ia = (a.x - x0) + ((a.y - y0) * W), ib = (b.x - x0) + ((b.y - y0) * W);
    if      ( (b.x == a.x + 1) && (b.y == a.y) ) { cn[ia] |= 1; cn[ib] |= 2; }
    else if ( (b.x == a.x - 1) && (b.y == a.y) ) { cn[ia] |= 2; cn[ib] |= 1; }
    else if ( (b.y == a.y + 1) && (b.x == a.x) ) { cn[ia] |= 4; cn[ib] |= 8; }
    else if ( (b.y == a.y - 1) && (b.x == a.x) ) { cn[ia] |= 8; cn[ib] |= 4; }
  }
  cps = xmalloc(((size_t)(2 * W) + 4) * sizeof(int));
  for (y = y1; y >= y0; y--) {
    ncp = 0;
    for (x = x0; x <= x1; x++) {
      int c = (x - x0) + ((y - y0) * W), ch;
      if      (!in[c])                          { ch = ' '; }
      else if ( (x == s.x) && (y == s.y) )      { ch = 's'; }
      else if ( (x == t.x) && (y == t.y) )      { ch = 't'; }
      else if (!P)                              { ch = '.'; }
      else {
        switch (cn[c]) {
          case 3:  ch = 0x2500; break;
          case 12: ch = 0x2502; break;
          case 9:  ch = 0x250c; break;
          case 10: ch = 0x2510; break;
          case 5:  ch = 0x2514; break;
          case 6:  ch = 0x2518; break;
          default: ch = '?';    break;
        }
      }
      cps[ncp++] = ch;
      if (x < x1) { cps[ncp++] = ( (cn[c] & 1) ? 0x2500 : ' ' ); }
    }
    while ( (ncp > 0) && (cps[ncp - 1] == ' ') ) { ncp--; }
    for (i = 0; i < ncp; i++) { bcp(&o, cps[i]); }
    if (y > y0) {
      bputs(&o, "\n");
      ncp = 0;
      for (x = x0; x <= x1; x++) {
        int c = (x - x0) + ((y - y0) * W);
        cps[ncp++] = ( (cn[c] & 8) ? 0x2502 : ' ' );
        if (x < x1) { cps[ncp++] = ' '; }
      }
      while ( (ncp > 0) && (cps[ncp - 1] == ' ') ) { ncp--; }
      for (i = 0; i < ncp; i++) { bcp(&o, cps[i]); }
      bputs(&o, "\n");
    }
  }
  if (!o.b) { bputs(&o, ""); }
  free(in);
  free(cn);
  free(cps);
  return o.b;
}

// json.dumps string (ensure_ascii): escapes, non-ASCII as \uXXXX.
//
static void json_str(Buf *o, const char *s) {
  const unsigned char *p = (const unsigned char *)s;
  char tmp[16];
  bputs(o, "\"");
  while (*p) {
    int cp = *p;
    if (cp >= 0x80) {
      if      ((cp & 0xe0) == 0xc0) { cp = ((cp & 0x1f) << 6) | (p[1] & 0x3f); p += 2; }
      else if ((cp & 0xf0) == 0xe0) { cp = ((cp & 0x0f) << 12) | ((p[1] & 0x3f) << 6) | (p[2] & 0x3f); p += 3; }
      else                          { p += 1; }
      snprintf(tmp, sizeof(tmp), "\\u%04x", cp);
      bputs(o, tmp);
      continue;
    }
    p++;
    if      (cp == '"')  { bputs(o, "\\\""); }
    else if (cp == '\\') { bputs(o, "\\\\"); }
    else if (cp == '\n') { bputs(o, "\\n"); }
    else if (cp == '\r') { bputs(o, "\\r"); }
    else if (cp == '\t') { bputs(o, "\\t"); }
    else if (cp < 0x20)  { snprintf(tmp, sizeof(tmp), "\\u%04x", cp); bputs(o, tmp); }
    else                 { tmp[0] = (char)cp; bput(o, tmp, 1); }
  }
  bputs(o, "\"");
}

static void pyfloat(Buf *o, double v) {
  char tmp[64];
  size_t k;
  snprintf(tmp, sizeof(tmp), "%.4f", v);
  k = strlen(tmp);
  while ( (k > 0) && (tmp[k - 1] == '0') ) { k--; }
  if ( (k > 0) && (tmp[k - 1] == '.') ) { k++; }
  tmp[k] = 0;
  if (strcmp(tmp, "-0.0") == 0) { strcpy(tmp, "0.0"); }
  bputs(o, tmp);
}

// The stats dict, in Python repr (q = '\'') or JSON (q = '"') form.
//
static void stats_dicts(Buf *o, const hpst_stats *st, char q, int which) {
  char tmp[128];
  int i;
  bputs(o, "{");
  if (which == 0) {
    for (i = 0; i < st->nco; i++) {
      int k = st->corder[i];
      snprintf(tmp, sizeof(tmp), "%s%c%s%c: %lld", (i ? ", " : ""), q, hpst_count_names[k], q,
               st->c[k]);
      bputs(o, tmp);
    }
  }
  else {
    for (i = 0; i < st->nto; i++) {
      int k = st->torder[i];
      snprintf(tmp, sizeof(tmp), "%s%c%s%c: ", (i ? ", " : ""), q, hpst_time_names[k], q);
      bputs(o, tmp);
      pyfloat(o, st->t[k]);
    }
  }
  bputs(o, "}");
}

// ---------------------------------------------------------------------------------------------
// Brute force for --check (port of lib/python/brute.py: DFS with connectivity, degree and
// colour pruning; exact).
// ---------------------------------------------------------------------------------------------

typedef struct {
  int  n, s, t, nunv;
  int *adj, *nadj;
  unsigned char *unv;
  int *stk;
  unsigned char *seen;
} Brute;

static int b_connected(Brute *b, int cur) {
  int sp = 0, cnt = 1, i, j;
  memset(b->seen, 0, (size_t)b->n);
  b->seen[cur] = 1;
  b->stk[sp++] = cur;
  while (sp > 0) {
    int u = b->stk[--sp];
    for (j = 0; j < b->nadj[u]; j++) {
      int v = b->adj[(4 * u) + j];
      if ( b->unv[v] && (!b->seen[v]) ) {
        b->seen[v] = 1;
        cnt++;
        b->stk[sp++] = v;
      }
    }
  }
  i = cnt;
  return ( i == (b->nunv + 1) );
}

static int b_degree(Brute *b, int cur) {
  int u, j;
  for (u = 0; u < b->n; u++) {
    int k = 0;
    if (!b->unv[u]) { continue; }
    for (j = 0; j < b->nadj[u]; j++) {
      int v = b->adj[(4 * u) + j];
      if ( b->unv[v] || (v == cur) ) { k++; }
    }
    if (k < ( (u == b->t) ? 1 : 2 )) { return 0; }
  }
  return 1;
}

static int b_dfs(Brute *b, int cur) {
  int j;
  if (b->nunv == 0) { return ( cur == b->t ); }
  if (!b_connected(b, cur)) { return 0; }
  if (!b_degree(b, cur)) { return 0; }
  for (j = 0; j < b->nadj[cur]; j++) {
    int v = b->adj[(4 * cur) + j];
    if (!b->unv[v]) { continue; }
    if ( (v == b->t) && (b->nunv > 1) ) { continue; }
    b->unv[v] = 0;
    b->nunv--;
    if (b_dfs(b, v)) { return 1; }
    b->unv[v] = 1;
    b->nunv++;
  }
  return 0;
}

// V sorted and unique. Returns 1 iff a Hamiltonian s-t path exists.
//
static int brute_hp(const PtVec *V, hpst_pt s, hpst_pt t) {
  Brute b;
  int i, j, n = V->n, blk = 0, wht, cs, ct, r;
  hpst_pt *ps, *pt_;
  if ( (!pv_has(V, s)) || (!pv_has(V, t)) || ( (s.x == t.x) && (s.y == t.y) ) ) { return 0; }
  if (n == 2) { return ( (abs(s.x - t.x) + abs(s.y - t.y)) == 1 ); }
  for (i = 0; i < n; i++) {
    if ((((V->v[i].x + V->v[i].y) % 2) + 2) % 2 == 0) { blk++; }
  }
  wht = n - blk;
  cs  = (((s.x + s.y) % 2) + 2) % 2;
  ct  = (((t.x + t.y) % 2) + 2) % 2;
  if ((n % 2) == 0) {
    if ( (cs == ct) || (blk != wht) ) { return 0; }
  }
  else {
    if (cs != ct) { return 0; }
    if ( (cs == 0) ? (blk != (wht + 1)) : (wht != (blk + 1)) ) { return 0; }
  }
  b.n    = n;
  b.adj  = xmalloc(((size_t)n) * 4 * sizeof(int));
  b.nadj = xmalloc(((size_t)n) * sizeof(int));
  b.unv  = xmalloc((size_t)n);
  b.seen = xmalloc((size_t)n);
  b.stk  = xmalloc(((size_t)n) * sizeof(int));
  for (i = 0; i < n; i++) {
    int dx[4] = { 1, -1, 0, 0 }, dy[4] = { 0, 0, 1, -1 };
    b.nadj[i] = 0;
    for (j = 0; j < 4; j++) {
      hpst_pt q;
      hpst_pt *f;
      q.x = V->v[i].x + dx[j];
      q.y = V->v[i].y + dy[j];
      f = bsearch(&q, V->v, (size_t)n, sizeof(hpst_pt), cmp_pt);
      if (f) { b.adj[(4 * i) + b.nadj[i]++] = (int)(f - V->v); }
    }
    b.unv[i] = 1;
  }
  ps  = bsearch(&s, V->v, (size_t)n, sizeof(hpst_pt), cmp_pt);
  pt_ = bsearch(&t, V->v, (size_t)n, sizeof(hpst_pt), cmp_pt);
  b.s = (int)(ps - V->v);
  b.t = (int)(pt_ - V->v);
  b.unv[b.s] = 0;
  b.nunv = n - 1;
  r = b_dfs(&b, b.s);
  free(b.adj); free(b.nadj); free(b.unv); free(b.seen); free(b.stk);
  return r;
}

// ---------------------------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------------------------

static const char *USAGE =
  "usage: hpst [-h] [--mode {fast}] [--draw] [--json] [--check] [--stats] [--no-heuristic]\n"
  "            [file]\n";

static char *read_all(FILE *f, size_t *len) {
  size_t cap = 1 << 16, n = 0, k;
  char *b = xmalloc(cap);
  while ((k = fread(b + n, 1, cap - n - 1, f)) > 0) {
    n += k;
    if ((n + 1) >= cap) {
      cap *= 2;
      b    = xrealloc(b, cap);
    }
  }
  b[n] = 0;
  *len = n;
  return b;
}

int main(int argc, char **argv) {
  const char *file = NULL;
  int f_draw = 0, f_json = 0, f_check = 0, f_stats = 0, f_noheur = 0, i;
  char *text;
  size_t len;
  PtVec V = { NULL, 0, 0 };
  int hs = 0, ht = 0, r, np = 0, rc = 0, chk = -1;
  hpst_pt s = { 0, 0 }, t = { 0, 0 }, *P = NULL;
  hpst_opts o;
  hpst_stats st;
  double t0, dt;
  const char *p;

  for (i = 1; i < argc; i++) {
    const char *a = argv[i];
    if      (strcmp(a, "--draw") == 0)         { f_draw = 1; }
    else if (strcmp(a, "--json") == 0)         { f_json = 1; }
    else if (strcmp(a, "--check") == 0)        { f_check = 1; }
    else if (strcmp(a, "--stats") == 0)        { f_stats = 1; }
    else if (strcmp(a, "--no-heuristic") == 0) { f_noheur = 1; }
    else if ( (strcmp(a, "-h") == 0) || (strcmp(a, "--help") == 0) ) {
      fputs(USAGE, stdout);
      fputs("\nDecide whether a solid grid graph has a Hamiltonian s-t path (Lean decideHamPath, fast"
            " mode, C port).\nInput: ASCII grid or JSON (see lib/README.md); default stdin.\n",
            stdout);
      return 0;
    }
    else if ( (strcmp(a, "--mode") == 0) || (strncmp(a, "--mode=", 7) == 0) ) {
      const char *m = NULL;
      if (a[6] == '=') { m = a + 7; }
      else if ((i + 1) < argc) { m = argv[++i]; }
      if ( (!m) || (strcmp(m, "fast") != 0) ) {
        fputs(USAGE, stderr);
        fprintf(stderr, "hpst: error: argument --mode: only 'fast' is available in the C port"
                " (ref mode: lib/python/hpst_cli.py --mode ref)\n");
        return 2;
      }
    }
    else if ( (a[0] == '-') && (a[1] != 0) ) {
      fputs(USAGE, stderr);
      fprintf(stderr, "hpst: error: unrecognized arguments: %s\n", a);
      return 2;
    }
    else if (!file) {
      file = a;
    }
    else {
      fputs(USAGE, stderr);
      fprintf(stderr, "hpst: error: unrecognized arguments: %s\n", a);
      return 2;
    }
  }

  if (file) {
    FILE *f = fopen(file, "rb");
    if (!f) {
      fprintf(stderr, "error: [Errno %d] %s: '%s'\n", errno, strerror(errno), file);
      return 2;
    }
    text = read_all(f, &len);
    fclose(f);
  }
  else {
    text = read_all(stdin, &len);
  }
  if (strlen(text) != len) {
    fprintf(stderr, "error: input contains a NUL byte\n");
    return 2;
  }
  for (p = text; ( (*p == ' ') || (*p == '\t') || (*p == '\n') || (*p == '\r') ||
                   (*p == '\v') || (*p == '\f') ); p++) { }
  if (*p == '{') { r = parse_json(text, &V, &hs, &s, &ht, &t); }
  else           { r = parse_ascii(text, &V, &hs, &s, &ht, &t); }
  free(text);
  if (!r) {
    fprintf(stderr, "error: %s\n", g_err);
    free(V.v);
    return 2;
  }
  pv_unique(&V);
  if ( (hs != 1) || (ht != 1) ) {
    if ( (hs == 0) || (ht == 0) ) {
      fprintf(stderr, "error: both endpoints s and t are required\n");
    }
    else {
      fprintf(stderr, "error: s and t must be points of V\n");
    }
    free(V.v);
    return 2;
  }
  if ( (!pv_has(&V, s)) || (!pv_has(&V, t)) ) {
    fprintf(stderr, "error: s and t must be points of V\n");
    free(V.v);
    return 2;
  }
  if ( (s.x == t.x) && (s.y == t.y) ) {
    fprintf(stderr, "error: s and t must differ\n");
    free(V.v);
    return 2;
  }
  if (!hpst_solid(V.v, V.n)) {
    fprintf(stderr, "error: V is not solid (it has a hole: a missing point that cannot reach the"
            " outside by king moves through missing points)\n");
    free(V.v);
    return 2;
  }

  hpst_default_opts(&o);
  o.heuristic = !f_noheur;
  t0 = now();
  r  = hpst_solve(V.v, V.n, s, t, &o, &P, &np, &st);
  dt = now() - t0;
  if (r < 0) {
    fprintf(stderr, "internal error: solver returned %d\n", r);
    return 1;
  }
  if ( (r == 1) && (!hpst_verify_path(V.v, V.n, s, t, P, np)) ) {
    fprintf(stderr, "internal error: invalid witness path\n");
    rc = 1;
  }
  if (f_check) {
    int B = brute_hp(&V, s, t);
    chk = ( (B == (r == 1)) ? 1 : 0 );
    if (!chk) { rc = 1; }
  }

  {
    Buf o2 = { NULL, 0, 0 };
    char tmp[64];
    char *dr = ( f_draw ? draw(&V, s, t, ( (r == 1) ? P : NULL ), np) : NULL );
    if (f_json) {
      bputs(&o2, "{\"answer\": ");
      bputs(&o2, ( (r == 1) ? "\"yes\"" : "\"no\"" ));
      bputs(&o2, ", \"path\": ");
      if (r == 1) {
        bputs(&o2, "[");
        for (i = 0; i < np; i++) {
          snprintf(tmp, sizeof(tmp), "%s[%d, %d]", (i ? ", " : ""), P[i].x, P[i].y);
          bputs(&o2, tmp);
        }
        bputs(&o2, "]");
      }
      else {
        bputs(&o2, "null");
      }
      if (f_check) {
        bputs(&o2, ", \"check\": ");
        bputs(&o2, ( chk ? "\"agree\"" : "\"DISAGREE\"" ));
      }
      if (f_stats) {
        bputs(&o2, ", \"stats\": {\"counts\": ");
        stats_dicts(&o2, &st, '"', 0);
        bputs(&o2, ", \"times\": ");
        stats_dicts(&o2, &st, '"', 1);
        bputs(&o2, ", \"branch\": ");
        json_str(&o2, st.branch);
        bputs(&o2, ", \"decided_by\": ");
        json_str(&o2, st.how);
        bputs(&o2, ", \"time\": ");
        pyfloat(&o2, dt);
        snprintf(tmp, sizeof(tmp), ", \"points\": %d}", V.n);
        bputs(&o2, tmp);
      }
      if (f_draw) {
        bputs(&o2, ", \"drawing\": ");
        json_str(&o2, dr);
      }
      bputs(&o2, "}\n");
    }
    else {
      bputs(&o2, ( (r == 1) ? "yes\n" : "no\n" ));
      if (r == 1) {
        for (i = 0; i < np; i++) {
          snprintf(tmp, sizeof(tmp), "%s%d,%d", (i ? " " : ""), P[i].x, P[i].y);
          bputs(&o2, tmp);
        }
        bputs(&o2, "\n");
      }
      if (f_draw) {
        bputs(&o2, dr);
        bputs(&o2, "\n");
      }
      if (f_check) {
        bputs(&o2, ( chk ? "check: agree (brute force)\n" : "check: DISAGREE (brute force)\n" ));
      }
      if (f_stats) {
        bputs(&o2, "stats counts: ");
        stats_dicts(&o2, &st, '\'', 0);
        bputs(&o2, "\nstats times: ");
        stats_dicts(&o2, &st, '\'', 1);
        bputs(&o2, "\nstats branch: ");
        bputs(&o2, st.branch);
        bputs(&o2, "\nstats decided_by: ");
        bputs(&o2, st.how);
        bputs(&o2, "\nstats time: ");
        pyfloat(&o2, dt);
        snprintf(tmp, sizeof(tmp), "\nstats points: %d\n", V.n);
        bputs(&o2, tmp);
      }
    }
    fwrite(o2.b, 1, o2.n, stdout);
    free(o2.b);
    free(dr);
  }
  free(P);
  free(V.v);
  return rc;
}

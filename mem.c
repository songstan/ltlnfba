/***** ltl_nf_ba : mem.c *****/

/* Written by Denis Oddoux, LIAFA, France                                 */
/* Copyright (c) 2001  Denis Oddoux                                       */
/* Modified by Paul Gastin, LSV, France                                   */
/* Copyright (c) 2007  Paul Gastin                                        */
/* Modified by Jun Song, Xi'an, China                                   */
/* Copyright (c) 2014  Jun Song                                        */
/*                                                                        */
/* This program is free software; you can redistribute it and/or modify   */
/* it under the terms of the GNU General Public License as published by   */
/* the Free Software Foundation; either version 2 of the License, or      */
/* (at your option) any later version.                                    */
/*                                                                        */
/* This program is distributed in the hope that it will be useful,        */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/* GNU General Public License for more details.                           */
/*                                                                        */
/* You should have received a copy of the GNU General Public License      */
/* along with this program; if not, write to the Free Software            */
/* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA*/
/*                                                                        */
/* Based on the translation algorithm by Gastin and Oddoux,               */
/* presented at the 13th International Conference on Computer Aided       */
/* Verification, CAV 2001, Paris, France.                                 */
/* Proceedings - LNCS 2102, pp. 53-65                                     */
/*                                                                        */
/* Send bug-reports and/or questions to Paul Gastin                       */
/* http://www.lsv.ens-cachan.fr/~gastin                                   */
/*                                                                        */
/* Some of the code in this file was taken from the Spin software         */
/* Written by Gerard J. Holzmann, Bell Laboratories, U.S.A.               */

#include "ltl_nf_ba.h"

#if 1
#define log(e, u, d)	event[e][(int) u] += (long) d;
#else
#define log(e, u, d)
#endif

#define A_LARGE		80
#define A_USER		0x55000000
#define NOTOOBIG	32768

#define POOL		0
#define ALLOC		1
#define FREE		2
#define NREVENT		3

extern	unsigned long All_Mem;
/*extern	int tl_verbose;*/
NFG_trans *nfg_list = (NFG_trans*)0;
CF_trans *cf_list = (CF_trans*)0;
/*ATrans *atrans_list = (ATrans *)0;
GTrans *gtrans_list = (GTrans *)0;
BTrans *btrans_list = (BTrans *)0;*/
CF_btrans *cbtrans_list = (CF_btrans*)0;

int aallocs = 0, afrees = 0, apool = 0;
int gallocs = 0, gfrees = 0, gpool = 0;
int ballocs = 0, bfrees = 0, bpool = 0;
int nallocs = 0, nfrees = 0, npool = 0;
int callocs = 0, cfrees = 0, cpool = 0;
int cfballocs = 0, cfbfrees = 0, cfbpool = 0;

union M {
	long size;
	union M *link;
};

static union M *freelist[A_LARGE];
static long	req[A_LARGE];
static long	event[NREVENT][A_LARGE];

void *
tl_emalloc(int U)
{	union M *m;
  	long r, u;
	void *rp;

	u = (long) ((U-1)/sizeof(union M) + 2);

	if (u >= A_LARGE)
	{	log(ALLOC, 0, 1);
		/*if (tl_verbose)
		printf("tl_spin: memalloc %ld bytes\n", u);*/
		m = (union M *) emalloc((int) u*sizeof(union M));
		All_Mem += (unsigned long) u*sizeof(union M);
	} else
	{	if (!freelist[u])
		{	r = req[u] += req[u] ? req[u] : 1;
			if (r >= NOTOOBIG)
				r = req[u] = NOTOOBIG;
			log(POOL, u, r);
			freelist[u] = (union M *)
				emalloc((int) r*u*sizeof(union M));
			All_Mem += (unsigned long) r*u*sizeof(union M);
			m = freelist[u] + (r-2)*u;
			for ( ; m >= freelist[u]; m -= u)
				m->link = m+u;
		}
		log(ALLOC, u, 1);
		m = freelist[u];
		freelist[u] = m->link;
	}
	m->size = (u|A_USER);

	for (r = 1; r < u; )
		(&m->size)[r++] = 0;

	rp = (void *) (m+1);
	memset(rp, 0, U);
	return rp;
}

void
tfree(void *v)
{	union M *m = (union M *) v;
	long u;

	--m;
	if ((m->size&0xFF000000) != A_USER)
		Fatal("releasing a free block", (char *)0);

	u = (m->size &= 0xFFFFFF);
	if (u >= A_LARGE)
	{	log(FREE, 0, 1);
		/* free(m); */
	} else
	{	log(FREE, u, 1);
		m->link = freelist[u];
		freelist[u] = m;
	}
}

/**********************************************************************************
 * function:  allocate the memory of the new NFG
 **********************************************************************************/
NFG_trans* emalloc_NFG_trans(){
	NFG_trans *newOne;
	if(!nfg_list){
		newOne  = (NFG_trans*)tl_emalloc(sizeof(NFG_trans));
		/*newOne->current = create_the_set();*/
		/*newOne->point = create_the_set();*/

		newOne->condition = create_the_set();
		newOne->point = (NFG*)0;
		/*newOne->redund = 0;*/
		newOne->final = create_the_set();
		/*clear_the_set(newOne->final);*/
		newOne->next = (NFG_trans*)0;
		npool++;
	}else{
		newOne = nfg_list;
		nfg_list = nfg_list->next;
		newOne->next = (NFG_trans*)0;
	}
	nallocs++;
	return newOne;
}
void free_nfg_trans(NFG_trans *list,int rec){
	if(!list){
		return;
	}
	if(rec){
		free_nfg_trans(list->next,rec);
	}
	list->next = nfg_list;
	nfg_list = list;
	nfrees++;
}
void free_nfg_trans_list(NFG_trans *a1,NFG_trans *a2,int rec){
	  nfrees++;
	  if(a1 && (a1 != a2)) {
		    if(rec){
		    	a1->point->incoming--;
		    }
		  free_nfg_trans_list(a1->next,a2,rec);
	  }
	  a1->next = nfg_list;
	  nfg_list = a1;
}
CF_trans* emalloc_CF_trans(){
	CF_trans *newOne;
	if(!cf_list){
		newOne = (CF_trans*)tl_emalloc(sizeof(CF_trans));
		newOne->condition = create_the_set();
		newOne->point = create_the_set();
		/*newOne->redund = 0;*/
		newOne->next = (CF_trans*)0;
		cpool++;
	}else{
		newOne = cf_list;
		cf_list = cf_list->next;
		newOne->next = (CF_trans*)0;
	}
	callocs++;
	return newOne;
}
void free_cf_trans(CF_trans *list, int rec){
	if(!list){
		return ;
	}
	if(rec){
		free_cf_trans(list->next,rec);
	}
	list->next = cf_list;
	cf_list = list;
	cfrees++;
}
void free_all_CF_trans(){
	CF_trans *c;
	while(cf_list){
		c = cf_list;
		cf_list = cf_list->next;
		tfree(c->condition);
		tfree(c->point);
		/*tfree(c->redund);*/
		tfree(c);

	}
}
CF_btrans* emalloc_cf_btrans() {
  CF_btrans *newOne;
  if(!cbtrans_list) {
    newOne = (CF_btrans *)tl_emalloc(sizeof(CF_btrans));
    newOne->condition = create_the_set();
    clear_the_set(newOne->condition);
    newOne->point = (CF_bstate*)0;
    cfbpool++;
  }
  else {
    newOne = cbtrans_list;
    cbtrans_list = cbtrans_list->next;
  }
  cfballocs++;
  return newOne;
}

void free_cf_btrans(CF_btrans *t, CF_btrans *sentinel, int fly) {
  cfbfrees++;
  if(sentinel && (t != sentinel)) {
    free_cf_btrans(t->next, sentinel, fly);
    if(fly) t->point->incoming--;
  }
  t->next = cbtrans_list;
  cbtrans_list = t;
}
/*
ATrans* emalloc_atrans() {
  ATrans *result;
  if(!atrans_list) {
    result = (ATrans *)tl_emalloc(sizeof(GTrans));
    result->pos = new_set(1);
    result->neg = new_set(1);
    result->to  = new_set(0);
    apool++;
  }
  else {
    result = atrans_list;
    atrans_list = atrans_list->nxt;
    result->nxt = (ATrans *)0;
  }
  aallocs++;
  return result;
}

void free_atrans(ATrans *t, int rec) {
  if(!t) return;
  if(rec) free_atrans(t->nxt, rec);
  t->nxt = atrans_list;
  atrans_list = t;
  afrees++;
}

void free_all_atrans() {
  ATrans *t;
  while(atrans_list) {
    t = atrans_list;
    atrans_list = t->nxt;
    tfree(t->to);
    tfree(t->pos);
    tfree(t->neg);
    tfree(t);
  }
}
*/
/*
GTrans* emalloc_gtrans() {
  GTrans *result;
  if(!gtrans_list) {
    result = (GTrans *)tl_emalloc(sizeof(GTrans));
    result->pos   = new_set(1);
    result->neg   = new_set(1);
    result->final = new_set(0);
    gpool++;
  }
  else {
    result = gtrans_list;
    gtrans_list = gtrans_list->nxt;
  }
  gallocs++;
  return result;
}

void free_gtrans(GTrans *t, GTrans *sentinel, int fly) {
  gfrees++;
  if(sentinel && (t != sentinel)) {
    free_gtrans(t->nxt, sentinel, fly);
    if(fly) t->to->incoming--;
  }
  t->nxt = gtrans_list;
  gtrans_list = t;
}

BTrans* emalloc_btrans() {
  BTrans *result;
  if(!btrans_list) {
    result = (BTrans *)tl_emalloc(sizeof(BTrans));
    result->pos = new_set(1);
    result->neg = new_set(1);
    bpool++;
  }
  else {
    result = btrans_list;
    btrans_list = btrans_list->nxt;
  }
  ballocs++;
  return result;
}

void free_btrans(BTrans *t, BTrans *sentinel, int fly) {
  bfrees++;
  if(sentinel && (t != sentinel)) {
    free_btrans(t->nxt, sentinel, fly);
    if(fly) t->to->incoming--;
  }
  t->nxt = btrans_list;
  btrans_list = t;
}
*/
void
a_stats(void)
{	long	p, a, f;
	int	i;

	printf(" size\t  pool\tallocs\t frees\n");

	for (i = 0; i < A_LARGE; i++)
	{	p = event[POOL][i];
		a = event[ALLOC][i];
		f = event[FREE][i];

		if(p|a|f)
		printf("%5d\t%6ld\t%6ld\t%6ld\n",
			i, p, a, f);
	}

	printf("cf\t%6d\t%6d\t%6d\n",
	       cpool, callocs, cfrees);
	printf("nfg\t%6d\t%6d\t%6d\n",
	       npool, nallocs, nfrees);
	printf("btrans\t%6d\t%6d\t%6d\n",
		       cfbpool, cfballocs, cfbfrees);
	/*printf("atrans\t%6d\t%6d\t%6d\n",
	       apool, aallocs, afrees);
	printf("gtrans\t%6d\t%6d\t%6d\n", 
	       gpool, gallocs, gfrees);
	printf("btrans\t%6d\t%6d\t%6d\n", 
	       bpool, ballocs, bfrees);*/

}

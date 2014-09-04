
/* Written by Jun Song, Xi'an, China                                   */
/* Copyright (c) 2014  Jun Song                                        */
#include "ltl_nf_ba.h"
/**********************************************************************************
 * global variables
 **********************************************************************************/
extern FILE *tl_out;
extern int  tl_stats;
extern int tl_print_ba;
struct rusage tr_debut, tr_fin;
struct timeval t_diff;
int node_num,the_set_size,node_table_ID;
int has_decomposed = 0;
Node **node_table;
int *final_table;
int final_table_ID=0;
CF_trans **cf_form;
/*int **is_decomposed;*/
int mode = 8 * sizeof(int);
int transition = 0;
int graph_ID = 0,true_graph_ID = 0;
/*int NF_num = 0;*/
/*NFG **all_graph;*/
FILE *dot;
NFG *head,*tail,*cursor;
NFG *NFG_stack,*NFG_remove,**init;
NFGScc *nfg_scc_stack;
int *fin,compute_directly,post_pone;
int nfg_scc_ID,*bad_nfg_scc,nfg_scc_size,nfg_rank,*the_final_set;
int *all_GF_components, *GF_form,*FG_form;
int inti_size = 0;
/**********************************************************************************
 * function:  check whether the node tree contain the time operator
 **********************************************************************************/
int check(Node *p)
{
	int sen = 1,beiju = 0;
	Node *tmp;
	for(tmp = p;tmp;tmp = tmp->lft)
	{
		if(tmp->ntyp == U_OPER || tmp->ntyp == V_OPER|| tmp->ntyp == NEXT)
		{
			sen = 0;
			return sen;
		}
		if(tmp->rgt){
			sen = check(tmp->rgt);
			if(sen==0){
				return sen;
			}
		}

	}
	return sen;
}
/*test if the formula has the GF_form*/
int check_always(Node *p){
	if (!p) return 0;
	if(p->ntyp==V_OPER&&p->lft&&p->lft->ntyp==FALSE){
		return 1;
	}
	return 0;
}
int check_sometimes(Node *p){
	if(!p) return 0;
	if(p->ntyp==U_OPER&&p->lft&&p->lft->ntyp==TRUE){
		return 1;
	}
	return 0;
}
int check_GF_form(Node *p){
	if(!p) return 0;
	if(check_always(p)&&p->rgt&&check_sometimes(p->rgt)){
		return 1;
	}
	return 0;
}

/*test is the the formula is GFp1&&GFp2&&...&&GFpn*/
int is_GF_inside(Node *p){
	if(!p) return 0;
	switch(p->ntyp){
	case OR:
		return check(p->rgt)&&check(p->lft);
		break;
	case AND:
		return is_GF_inside(p->lft)&&is_GF_inside(p->rgt);
		break;
	case U_OPER:
		if(check_sometimes(p)&&check(p->rgt)){
			return 1;
		}else return 0;
		break;
	case V_OPER:
		return 0;
		break;
	case NEXT:
		return 0;
		break;
	case NOT:
		return is_GF_inside(p->lft);
		break;
	case FALSE:
	case TRUE:
	case PREDICATE:
		return 1;
		break;
	default:
		printf("Unknown token:");
		tl_explain(p->ntyp);
		break;
	}
	return 0;
}
int check_all_GF_components(Node *p){
	if(!p) return 0;
	if(!check_always(p)) return 0;
	if(is_GF_inside(p->rgt)) return 1;
	return 0;
}
int is_true_GF_inside(Node *p){
	if(!p) return 0;
	switch(p->ntyp){
	case OR:
		return 0;
		break;
	case AND:
		return is_true_GF_inside(p->lft)&&is_true_GF_inside(p->rgt);
		break;
	case U_OPER:
		if(check_sometimes(p)){
			return 1;
		}else return 0;
		break;
	case V_OPER:
		return 0;
		break;
	case NEXT:
		return 0;
		break;
	case NOT:
		return 0;
		break;
	case FALSE:
	case TRUE:
	case PREDICATE:
		return 0;
		break;
	default:
		printf("Unknown token:");
		tl_explain(p->ntyp);
		break;

	}
	return 0;
}
int is_true_GF_inside1(Node *p){
	if(!p) return 0;
	switch(p->ntyp){
	case OR:
		return 0;
		break;
	case AND:
		return 0;
		break;
	case U_OPER:
		return 0;
	case V_OPER:
		if(check_always(p)){
			return 1;
		}else return 0;
		break;
		break;
	case NEXT:
		return 0;
		break;
	case NOT:
		return 0;
		break;
	case FALSE:
	case TRUE:
	case PREDICATE:
		return 0;
		break;
	default:
		printf("Unknown token:");
		tl_explain(p->ntyp);
		break;

	}
	return 0;
}
int check_all_true_GF_components(Node *p){
	if(!p) return 0;
	if(check_always(p)&&is_true_GF_inside(p->rgt)) return 1;
	/*if(check_sometimes(p)&&is_true_GF_inside1(p->rgt)) return 1;*/
	return 0;
}
int check_all_FG_components(Node *p){
	if(!p) return 0;
	if(check_sometimes(p)&&is_true_GF_inside1(p->rgt)) return 1;
	return 0;
}
int check_until(Node *p){
	if(!p) return 0;
	if(p->ntyp==U_OPER){
		return 1;
	}
	return 0;
}
int check_release(Node *p){
	if(!p) return 0;
	if(p->ntyp==V_OPER){
		return 1;
	}
	return 0;
}
/*test if the node has the next operator*/
int check_next(Node *p)
{
	int sen = 1,beiju = 0;
	Node *tmp;
	for(tmp = p;tmp;tmp = tmp->lft)
	{
		if(tmp->ntyp == NEXT)
		{
			sen = 0;
			return sen;
		}
		if(tmp->rgt){
			sen = check_next(tmp->rgt);
			if(sen==0){
				return sen;
			}
		}

	}
	return sen;
}

int only_next(Node *p)
{
	int sen = 1,beiju = 0;
	Node *tmp;
	for(tmp = p;tmp;tmp = tmp->lft)
	{
		if(tmp->ntyp == U_OPER || tmp->ntyp == V_OPER)
		{
			sen = 0;
			return sen;
		}
		if(tmp->rgt){
			sen = only_next(tmp->rgt);
			if(sen==0){
				return sen;
			}
		}

	}
	return sen;
}
/**********************************************************************************
 * function:  duplicate a node
 **********************************************************************************/
Node *copy_one_node(Node *p){
	Node *n;
	if (!p) return p;

	n =  (Node *) tl_emalloc(sizeof(Node));
	n->ntyp = p->ntyp;
	n->sym  = p->sym; /*need to be modified*/
	n->lft  = p->lft;
	n->rgt  = p->rgt;

	return n;
}
Node *copy_the_node(Node *p){
	Node *n;
	if (!p) return p;
	n = getnode(p);
	n->lft = dupnode(p->lft);
	n->rgt = dupnode(p->rgt);
	return n;
}

/**********************************************************************************
 * function:  calculate the node's size
 **********************************************************************************/
int calculate_node_size(Node *p) /* returns the number of temporal nodes */
{
  switch(p->ntyp) {
  case AND:
  case OR:
  case U_OPER:
  case V_OPER:
    return(calculate_node_size(p->lft) + calculate_node_size(p->rgt) + 1);
#ifdef NXT
  case NEXT:
    return(calculate_node_size(p->lft) + 1);
#endif
  default:
    return 1;
    break;
  }
}
int calculate_nodetree_szie(Node *p){
	switch(p->ntyp) {
	  case AND:
	  case OR:
	  case U_OPER:
	  case V_OPER:
	    return(calculate_node_size(p->lft) + calculate_node_size(p->rgt) + 1);
	#ifdef NXT
	  case NEXT:
	    return(calculate_node_size(p->lft) + 1);
	#endif
	  default:
	    return 1;
	    break;
	  }
}
/**********************************************************************************
 * function:  create the set
 **********************************************************************************/
int* create_the_set(){
	return (int*)tl_emalloc(the_set_size*sizeof(int));
}




/**********************************************************************************
 * function:  merge the two sets
 **********************************************************************************/
void merge_the_sets(int *left,int *right){
	int i;
	for(i = 0; i < the_set_size; i++){
		left[i] = left[i] | right[i];
	}
}
void do_merge_the_set(int *new,int *left,int *right){
	int i;
	for(i = 0; i < the_set_size; i++){
		new[i] = left[i] | right[i];
	}
}
/**********************************************************************************
 * function:  test whether the two sets is the same or not
 **********************************************************************************/
int test_same_sets(int *left,int *right){
	int i,test = 1;
	for(i = 0; i < the_set_size; i++){
		test &= (left[i] == right[i]);
	}
	return test;
}

/**********************************************************************************
 * function:  test whether the left set is contained in the right set
 *            check if the right one contain the left one
 **********************************************************************************/
int test_is_contain(int *left,int *right){
	int i,test = 0;
	for(i = 0; i < the_set_size; i++){
		test |= (left[i] & ~right[i]);
	}
	return !test;
}
/**********************************************************************************
 * function:  test the intersection of the two sets
 **********************************************************************************/
int test_intersect(int *left, int *right){
	int i,test = 0;
	for(i = 0; i < the_set_size; i++){
		test |= (left[i] & right[i]);
	}
	return !test;
}
/**********************************************************************************
 * function:  initial the set
 **********************************************************************************/
int* clear_the_set(int *table){
	int i;
	for(i = 0; i < the_set_size; i++) {
		table[i] = 0;
	}
	return table;
}

/**********************************************************************************
 * function:  add an element in set
 **********************************************************************************/
void add_the_set(int *table,int n){
	table[n/mode] |= 1<<(n%mode);
}

/**********************************************************************************
 * function:  copy the  set
 **********************************************************************************/
void copy_the_set(int *to,int *from){
	int i;
	for(i = 0; i < the_set_size; i++){
	    to[i] = from[i];
	}
}
/**********************************************************************************
 * function:  remove the element from the set
 **********************************************************************************/
void rem_the_set(int *table,int i){
	table[i/mode] &= (-1 - (1 << (i%mode)));
}
/**********************************************************************************
 * function:  test if the element is in the set
 **********************************************************************************/
int in_the_set(int *set,int element){
	return (set[element/mode]&(1<<(element%mode)));
}
/**********************************************************************************
 * function:  print the elements in the set
 **********************************************************************************/
void print_the_set(int *table){
	int i,j,start = 1;
	int number = -1;
	for(i = 0; i < the_set_size; i++){
	    for(j = 0; j < mode; j++){
	    	 if(table[i] & (1 << j)){
	    		 if(!start){
	    			 printf(",");
	    		 }
	    		 number = mode * i + j;
	    		 printf("%d",number);
	    		 start = 0;
	    	 }
	    }
	}
	if(number==-1){
		printf("0==%d",0);
	}
}
/**********************************************************************************
 * function:  find the node in the set
 **********************************************************************************/
Node* print_the_node(int *table){
	int i,j,start = 1;
	int number = -1;
	Node *result = (Node*)0;
	for(i = 0; i < the_set_size; i++){
	    for(j = 0; j < mode; j++){
	    	 if(table[i] & (1 << j)){
	    		 number = mode * i + j;
	    		 if(!start){
	    			 /*Node *one = dupnode(node_table[number]);*/
	    			 result = tl_nn(AND,result,node_table[number]);
	    		 }else{
	    			 /*Node *one = dupnode(node_table[number]);*/
	    			 result = node_table[number];
	    		 }
	    		 number = 0;
	    		 start = 0;
	    	 }
	    }
	}
	if(number == -1){
		result = node_table[0];
	}
	/*printf("print the node is:\n");
	dump(result);
	printf("\n");
	*/
	return result;
}
/**********************************************************************************
 * function:  delete an element in set
 **********************************************************************************/
void del_the_set(int *table,int n){
	table[n/mode] &= (-1-(1<<(n%mode)));
}

/**********************************************************************************
 * function:  judge if the node has been decomposed
 **********************************************************************************/
/*
int be_decomposed(int *table){
	int i;
	for(i=0;i<has_decomposed;i++){
		if(test_same_sets(table,is_decomposed[i])){
			return i;
		}
	}
	return -1;
}
*/
/**********************************************************************************
 * function:  judge if the transition has been added in the array
 **********************************************************************************/

/**********************************************************************************
 * function:  initial the node table
 **********************************************************************************/
int is_add(Node* p){
	int i;
	for(i=0;i<node_table_ID;i++){
		if(p->ntyp==TRUE&&node_table[i]->ntyp==TRUE){
			return i;
		}
		if(isequal(p,node_table[i])){
			return i;
		}

	}
	return -1;
}
void add_in_state_table(Node *p){
	int all_GF = 0,GF_f = 0;
	if(p){
		if(is_add(p)>=0){
			return ;
		}
		switch(p->ntyp){
		case TRUE:
			break;
		case FALSE:
			break;
		case PREDICATE:
			break;
		case NOT:
			break;
		case NEXT:
			add_in_state_table(p->lft);
			break;
		case AND:
			add_in_state_table(p->lft);
			add_in_state_table(p->rgt);
			break;
		case OR:
			add_in_state_table(p->lft);
			add_in_state_table(p->rgt);
			break;
		case U_OPER:
			add_in_state_table(p->lft);
			add_in_state_table(p->rgt);
			final_table[final_table_ID++] = node_table_ID;
			break;
		case V_OPER:
			/*
			if(check_all_GF_components(p)){
				all_GF = 1;
			}
			if(check_GF_form(p)){
				GF_f = 1;
			}
			*/
			add_in_state_table(p->lft);
			add_in_state_table(p->rgt);
			break;
		default:
			break;
		}
		node_table[node_table_ID++] = p;
		/*
		if(all_GF==1){
			add_set(all_GF_components,node_table_ID);
			all_GF = 0;
		}
		if(GF_f==1){
			add_set(GF_form,node_table_ID);
			GF_f = 0;
		}
		*/

		/*printf("Node :\n");
		dump(p);
		printf("\n node number is %d\n",node_table_ID-1);*/
	}
}
void initial_node_table(Node *p){
	node_table[node_table_ID++] = True;
	add_in_state_table(p);
}

int index_of_table(Node *p){
	if(!p) return -1;
	int i;
	for(i=0;i<node_table_ID;i++){
		if(p->ntyp==TRUE&&node_table[i]->ntyp==TRUE){
			return i;
		}
		if(isequal(node_table[i],p)){
			return i;
		}
	}
	return -1;
}

/**********************************************************************************
 * function:  merge the two CF_trans
 **********************************************************************************/
void do_merge_CF_trans(CF_trans **new,CF_trans *left,CF_trans *right){
	if(!left||!right){
		free_cf_trans(*new,0);
		*new = (CF_trans*)0;
		return ;
	}
	if(!*new){
		*new = emalloc_CF_trans();
	}
	do_merge_the_set((*new)->point,left->point,right->point);
	do_merge_the_set((*new)->condition,left->condition,right->condition);
}

CF_trans *merge_CF_trans(CF_trans *left,CF_trans *right){
	CF_trans *new = emalloc_CF_trans();
	do_merge_CF_trans(&new,left,right);
	return new;
}
/**********************************************************************************
 * function:  merge the two NFGs
 **********************************************************************************/
void do_merge_NFG_trans(NFG_trans **new,NFG_trans *left,NFG_trans *right){
	if(!left||!right){
		free_nfg_trans(*new,0);
		*new = (NFG_trans*)0;
		return ;
	}
	if(!*new){
		*new = emalloc_NFG_trans();
	}
	do_merge_the_set((*new)->condition,left->condition,right->condition);
}

NFG_trans *merge_NFG_trans(NFG_trans *left,NFG_trans *right){
	NFG_trans *new = emalloc_NFG_trans();
	do_merge_NFG_trans(&new,left,right);
	return new;
}

/**********************************************************************************
 * function:  duplicate the set
 **********************************************************************************/
NFG_trans* dup_NFG_trans(NFG_trans *n){
	NFG_trans *newOne;
	if(!n){
		return n;
	}
	newOne = emalloc_NFG_trans();
	copy_the_set(newOne->condition,n->condition);
	return newOne;
}
void copy_the_NFG_trans(NFG_trans *to,NFG_trans *from){
	to->point = from->point;
	copy_the_set(to->condition,from->condition);
	copy_the_set(to->final,from->final);
}

/**********************************************************************************
 * function:  duplicate the set
 **********************************************************************************/
CF_trans* dup_CF_trans(CF_trans *n){
	CF_trans *newOne;
	if(!n){
		return n;
	}
	newOne = emalloc_CF_trans();
	/*copy_the_set(newOne->current,n->current);*/
	copy_the_set(newOne->point,n->point);
	copy_the_set(newOne->condition,n->condition);
	return newOne;
}
CF_trans *copy_the_CF_trans(CF_trans *from){
	CF_trans *c = (CF_trans*)0;
	CF_trans *resource;
	for(resource=from;resource;resource=resource->next){
		CF_trans *tmp = dup_CF_trans(resource);
		tmp->next = c;
		c = tmp;
	}
	return c;
}
/**********************************************************************************
 * function:  simplify the graph
 **********************************************************************************/
/*
void simplify_the_NFG(NFG_trans *list){
	printf("\n --------------------------jian hua \n");
	NFG_trans *n1 = (NFG_trans*)0;
	NFG_trans *n2 = (NFG_trans*)0;
	for(n1=list;n1;n1=n1->next){
		for(n2=n1->next;n2;n2=n2->next){
			if(test_same_sets(n1->point,n2->point)){
				if(test_is_contain(n1->condition,n2->condition)){
					n2->redund = 1;
				}else if(test_is_contain(n2->condition,n1->condition)){
					n1->redund = 1;
				}
			}
		}

	}
}
*/
/**********************************************************************************
 * function:  free the NFG
 **********************************************************************************/
void free_NFG(NFG *one){
	free_nfg_trans_list(one->trans->next,one->trans,1);
	tfree(one->current);
	tfree(one);
}
/**********************************************************************************
 * function:  generate the CF normal form form the syntax tree
 **********************************************************************************/
Node *NF(Node *p){
	/*NF_num++;*/
	if(!p) return ;


	switch(p->ntyp){
	case NOT:
		p = tl_nn(AND,p,tl_nn(NEXT,True,ZN));
		break;
	case NEXT:
		/*if(check(p->lft)){*/
			p = tl_nn(AND,True,p);
			break;
		/*}*/
		/*if(!check(p->lft)){
			p = tl_nn(AND,True,tl_nn(NEXT,NF(p->lft),ZN));
			break;
		}*/
		break;
	case AND:
		if(check(p->lft) && p->rgt->ntyp == NEXT)/*maybe need to be deeper decomposed*/
		{
			break;
		}
		if(!check_next(p->lft)&&only_next(p->lft)&&p->rgt->ntyp==NEXT){
			break;
		}
		if(!check_next(p->lft)&&p->rgt->ntyp==NEXT){
			p = tl_nn(AND,NF(p->lft),p->rgt);
			break;
		}
		if(check(p->lft) && check(p->rgt)){
			p = tl_nn(AND,p,tl_nn(NEXT,True,ZN));
			break;
		}
		p = tl_nn(AND,NF(p->lft),NF(p->rgt));
		break;

	case OR:
		p = tl_nn(OR,NF(p->lft),NF(p->rgt));
		break;

	case U_OPER:
		if(check(p->lft)){
			p = tl_nn(OR,NF(p->rgt),tl_nn(AND,p->lft,tl_nn(NEXT,p,ZN)));
			break;
		}
		p = tl_nn(OR,NF(p->rgt),tl_nn(AND,NF(p->lft),tl_nn(NEXT,p,ZN)));
		break;

	case V_OPER:
		if(!(check(p->lft)) && (check(p->rgt) == 1)){
			p = tl_nn(OR,tl_nn(AND,p->rgt,NF(p->lft)),tl_nn(AND,p->rgt,tl_nn(NEXT,p,ZN)));
			break;
		}
		if(check(p->lft)==1 && !check(p->rgt)){
			p = tl_nn(OR,tl_nn(AND,p->lft,NF(p->rgt)),tl_nn(AND,NF(p->rgt),tl_nn(NEXT,p,ZN)));
			break;
		}
		if(check(p->lft)==1 && check(p->rgt)==1){
			p = tl_nn(OR,tl_nn(AND,tl_nn(AND,p->lft,p->rgt),tl_nn(NEXT,True,ZN)),tl_nn(AND,p->rgt,tl_nn(NEXT,p,ZN)));
			break;
		}
		p = tl_nn(OR,tl_nn(AND,NF(p->rgt),NF(p->lft)),tl_nn(AND,NF(p->rgt),tl_nn(NEXT,p,ZN)));
		break;

	case PREDICATE:
		p = tl_nn(AND,p,tl_nn(NEXT,True,ZN));
		break;

	case FALSE:
		p = tl_nn(AND,p,tl_nn(NEXT,False,ZN));
		break;
	case TRUE:
		p = tl_nn(AND,p,tl_nn(NEXT,True,ZN));
		break;
	}
	return p;
}

Node *NF_normal(Node *p){
	/*NF_num++;*/
	if(!p) return ;


	switch(p->ntyp){
	case NOT:
		p = tl_nn(AND,p,tl_nn(NEXT,True,ZN));
		break;
	case NEXT:
		/*if(check(p->lft)){*/
			p = tl_nn(AND,True,p);
			break;
		/*}*/
		/*if(!check(p->lft)){
			p = tl_nn(AND,True,tl_nn(NEXT,NF(p->lft),ZN));
			break;
		}*/
		break;
	case AND:
		if(check(p->lft) && p->rgt->ntyp == NEXT)/*maybe need to be deeper decomposed*/
		{
			break;
		}
		if(!check_next(p->lft)&&only_next(p->lft)&&p->rgt->ntyp==NEXT){
			break;
		}
		if(!check_next(p->lft)&&p->rgt->ntyp==NEXT){
			p = tl_nn(AND,NF_normal(p->lft),p->rgt);
			break;
		}
		if(check(p->lft) && check(p->rgt)){
			p = tl_nn(AND,p,tl_nn(NEXT,True,ZN));
			break;
		}
		p = tl_nn(AND,NF_normal(p->lft),NF_normal(p->rgt));
		break;

	case OR:
		p = tl_nn(OR,NF_normal(p->lft),NF_normal(p->rgt));
		break;

	case U_OPER:
		if(check_all_FG_components(p)){
			p = tl_nn(AND,True,tl_nn(NEXT,p,ZN));
			break;
		}
		if(check(p->lft)){
			p = tl_nn(OR,NF_normal(p->rgt),tl_nn(AND,p->lft,tl_nn(NEXT,p,ZN)));
			break;
		}
		p = tl_nn(OR,NF_normal(p->rgt),tl_nn(AND,NF_normal(p->lft),tl_nn(NEXT,p,ZN)));
		break;

	case V_OPER:
		if(check_all_true_GF_components(p)){
			p = tl_nn(AND,True,tl_nn(NEXT,p,ZN));
			break;
		}
		if(!(check(p->lft)) && (check(p->rgt) == 1)){
			p = tl_nn(OR,tl_nn(AND,p->rgt,NF_normal(p->lft)),tl_nn(AND,p->rgt,tl_nn(NEXT,p,ZN)));
			break;
		}
		if(check(p->lft)==1 && !check(p->rgt)){
			p = tl_nn(OR,tl_nn(AND,p->lft,NF_normal(p->rgt)),tl_nn(AND,NF_normal(p->rgt),tl_nn(NEXT,p,ZN)));
			break;
		}
		if(check(p->lft)==1 && check(p->rgt)==1){
			p = tl_nn(OR,tl_nn(AND,tl_nn(AND,p->lft,p->rgt),tl_nn(NEXT,True,ZN)),tl_nn(AND,p->rgt,tl_nn(NEXT,p,ZN)));
			break;
		}
		p = tl_nn(OR,tl_nn(AND,NF_normal(p->rgt),NF_normal(p->lft)),tl_nn(AND,NF_normal(p->rgt),tl_nn(NEXT,p,ZN)));
		break;

	case PREDICATE:
		p = tl_nn(AND,p,tl_nn(NEXT,True,ZN));
		break;

	case FALSE:
		p = tl_nn(AND,p,tl_nn(NEXT,False,ZN));
		break;
	case TRUE:
		p = tl_nn(AND,p,tl_nn(NEXT,True,ZN));
		break;
	}
	return p;
}

/**********************************************************************************
 * function:  traversal the CF node tree
 **********************************************************************************/
CF_trans *and_cf_form(CF_trans *left,CF_trans *right){
	CF_trans *n = (CF_trans*)0;
	CF_trans *n1,*n2;
	n1 = left;
	n2 = right;
	for(;n1;n1=n1->next){
		for(n2=right;n2;n2=n2->next){
			CF_trans *tmp = merge_CF_trans(n1,n2);
			if(tmp){
				tmp->next = n;
				n = tmp;
			}
		}
	}

	free_cf_trans(left,1);
	free_cf_trans(right,1);
	free_all_CF_trans();

	return n;
}
CF_trans *build_CF_trans(Node *p){

	CF_trans *n1 = (CF_trans *)0,*n2 = (CF_trans*)0;
	CF_trans *n = (CF_trans*)0;
	CF_trans *left,*right;
	switch(p->ntyp){
		case TRUE:
			n = emalloc_CF_trans();
			clear_the_set(n->point);
			clear_the_set(n->condition);
			break;
		case FALSE:
			break;
		case PREDICATE:
			n = emalloc_CF_trans();
			clear_the_set(n->point);
			clear_the_set(n->condition);
			add_the_set(n->condition,index_of_table(p));
			break;
		case NOT:
			n = emalloc_CF_trans();
			clear_the_set(n->point);
			clear_the_set(n->condition);
			add_the_set(n->condition,index_of_table(p));
			break;
		case AND:
			n = (CF_trans*)0;
			n1 = build_CF_trans(p->lft);
			n2 = build_CF_trans(p->rgt);
			left =n1;
			right = n2;
			for(;n1;n1=n1->next){
				for(n2=right;n2;n2=n2->next){
					CF_trans *tmp = merge_CF_trans(n1,n2);
					if(tmp){
						tmp->next = n;
						n = tmp;
					}
				}

			}
			free_cf_trans(left,1);
			free_cf_trans(right,1);
			/*free_all_atrans();*/
			break;
		case OR:
			n = (CF_trans*)0;
			n1 = build_CF_trans(p->lft);
			left = n1;
			for(;n1;n1=n1->next){
				CF_trans *tmp = dup_CF_trans(n1);
				tmp->next = n;
				n = tmp;
			}
			free_cf_trans(left,1);
			n2 = build_CF_trans(p->rgt);
			right = n2;
			for(;n2;n2=n2->next){
				CF_trans *tmp = dup_CF_trans(n2);
				tmp->next = n;
				n = tmp;
			}
			free_cf_trans(right,1);
			break;
		case NEXT:
			n = emalloc_CF_trans();
			clear_the_set(n->point);
			clear_the_set(n->condition);
			if(p->lft->ntyp!=TRUE){
				add_the_set(n->point,index_of_table(p->lft));
			}

			break;
		default:
			break;
		}
	return n;

}
/**********************************************************************************
 * function: initial the node's CF-normal form
 **********************************************************************************/
CF_trans* node_to_CF_form(int table_id){
	int i;
	/*printf("\n initial the CF:\n");*/

		Node *dup_one = dupnode(node_table[table_id]);
		/*if(check_all_GF_components(node_table[table_id])){
			add_the_set(all_GF_components,table_id);
		}*/
		if(check_all_true_GF_components(node_table[table_id])){
			/*add_the_set(GF_form,table_id);*/
			cf_form[table_id] = build_CF_trans(NF(dup_one));
		}else if(check_all_FG_components(node_table[table_id])){
			/*add_the_set(FG_form,table_id);*/
			cf_form[table_id] = build_CF_trans(NF(dup_one));
		}else{
			cf_form[table_id] = build_CF_trans(NF_normal(dup_one));
		}




		/*CF_trans *test;*/
		releasenode(1,dup_one);
		/*for(test=cf_form[i];test;test=test->next){
			printf("\n current state:\n");
			dump(dup_one);
			printf("\n");
			printf("next state:\n");
			Node *point = print_the_node(test->point);
			dump(point);
			printf("\n");
			printf("transform condition:\n");
			Node *condition = print_the_node(test->condition);
			dump(condition);
			printf("\n");
		}*/

	return cf_form[table_id];
	/*free_all_CF_trans();*/
	/*printf("end of initial;\n");*/
}

void initial_CF_form(){
	int i;
	/*printf("\n initial the CF:\n");*/
	for(i=0;i<node_table_ID;i++){

		/*Node *dup_one = dupnode(node_table[i]);*/
		if(check_all_GF_components(node_table[i])){
			add_the_set(all_GF_components,i);
		}
		if(check_all_true_GF_components(node_table[i])){
			add_the_set(GF_form,i);
			/*cf_form[i] = build_CF_trans(NF(dup_one));*/
		}else if(check_all_FG_components(node_table[i])){
			add_the_set(FG_form,i);
			/*cf_form[i] = build_CF_trans(NF(dup_one));*/
		}else{
			/*cf_form[i] = build_CF_trans(NF_normal(dup_one));*/
		}

			/*printf("*****initial the begin node\n");*/



		/*CF_trans *test;
		releasenode(1,dup_one);*/
		/*for(test=cf_form[i];test;test=test->next){
			printf("\n current state:\n");
			dump(dup_one);
			printf("\n");
			printf("next state:\n");
			Node *point = print_the_node(test->point);
			dump(point);
			printf("\n");
			printf("transform condition:\n");
			Node *condition = print_the_node(test->condition);
			dump(condition);
			printf("\n");
		}*/

	}
	/*free_all_CF_trans();*/
	/*printf("end of initial;\n");*/
}
/**********************************************************************************
 * function:  delete the redundant state and reposition the transition
 **********************************************************************************/
void retarget_all_NFG_trans(){
	if(tl_stats) getrusage(RUSAGE_SELF, &tr_debut);
	NFG *n;
	NFG_trans *t;
	for(n=head->next;n!=tail;n=n->next){
		for(t=n->trans->next;t!=n->trans;t=t->next){
			if(!t->point->trans){
				t->point = t->point->pre;
			}
		}
	}
	while(NFG_remove->next!=NFG_remove){
		n = NFG_remove->next;
		NFG_remove->next = NFG_remove->next->next;
		if(n->current){
			tfree(n->current);
		}
		/*if(n->final){
			tfree(n->final);
		}*/
		tfree(n);
	}
	if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "delete the GBAs' redundant state: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);

	}
}
/**********************************************************************************
 * function:  find the SCCs(strongly connected components) of the GBA
 **********************************************************************************/
NFG *remove_nfg_state(NFG *s,NFG*s1){
	  NFG *prv = s->pre;
	  s->pre->next = s->next;
	  s->next->pre = s->pre;
	  free_nfg_trans_list(s->trans->next, s->trans, 0);
	  s->trans = (NFG_trans *)0;
	  tfree(s->current);
	  s->current = 0;
	  s->next = NFG_remove->next;
	  NFG_remove->next = s;
	  s->pre = s1;
	  for(s1 = NFG_remove->next; s1 != NFG_remove; s1 = s1->next)
	    if(s1->pre == s)
	      s1->pre = s->pre;
	  return prv;
}

int nfg_dfs(NFG *s){
	NFG_trans *t;
	NFGScc *c;
	NFGScc *scc = (NFGScc *)tl_emalloc(sizeof(NFGScc));
	scc->nfg_state = s;
	scc->rank = nfg_rank;
	scc->theta = nfg_rank++;
	scc->next = nfg_scc_stack;
	nfg_scc_stack = scc;
	s->incoming = 1;
	for (t = s->trans->next; t != s->trans; t = t->next) {
	    if (t->point->incoming == 0) {
	    	int result = nfg_dfs(t->point);
	    	scc->theta = min(scc->theta, result);
	    }
	    else {
	    	for(c = nfg_scc_stack->next; c != (NFGScc*)0; c = c->next){
	    		if(c->nfg_state == t->point) {
	    			scc->theta = min(scc->theta, c->rank);
	    			break;
	    		}
	    	}
	    }
	}
	if(scc->rank == scc->theta) {
	    while(nfg_scc_stack != scc) {
	    	nfg_scc_stack->nfg_state->incoming = nfg_scc_ID;
	    	nfg_scc_stack = nfg_scc_stack->next;
	    }
	    scc->nfg_state->incoming = nfg_scc_ID++;
	    nfg_scc_stack = scc->next;
	}
	return scc->theta;

}
void nfg_scc(){
	if(tl_stats) getrusage(RUSAGE_SELF, &tr_debut);
	NFG  *s;
	NFG_trans *t;
	int i, **scc_final;
	nfg_rank = 1;
	nfg_scc_stack = (NFGScc*)0;
	nfg_scc_ID = 1;
	if(head == tail){
		return;
	}
	for(s = head->next; s != tail; s = s->next){
	    s->incoming = 0; /* state color = white */
	}
	nfg_dfs(head->next);
	scc_final = (int **)tl_emalloc(nfg_scc_ID * sizeof(int *));
	for(i = 0; i < nfg_scc_ID; i++){
	    scc_final[i] = create_the_set();
	}
	for(s = head->next; s != tail; s = s->next){
	    if(s->incoming == 0){
	      s = remove_nfg_state(s, 0);
	    }
	    else{
	      for (t = s->trans->next; t != s->trans; t = t->next){
	    	  if(t->point->incoming == s->incoming){
	    		  merge_the_sets(scc_final[s->incoming], t->final);
	        }
	      }
	    }
	}
	nfg_scc_size = (nfg_scc_ID + 1) / (8 * sizeof(int)) + 1;
	bad_nfg_scc=(int*)tl_emalloc(nfg_scc_size*sizeof(int));
	for(i = 0; i < nfg_scc_ID; i++){
		 if(!test_is_contain(the_final_set, scc_final[i])){
			 add_the_set(bad_nfg_scc, i);
			 /*printf("\n the bad SCC is %d\n",i);*/
		 }
	}
	for(i = 0; i < nfg_scc_ID; i++){
	    tfree(scc_final[i]);
	}
	tfree(scc_final);

	if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "find the GBAs' sccs: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);

	}
}
/**********************************************************************************
 * function:  simplify the all NFG_trans
 **********************************************************************************/
void simplify_all_NFG_trans(){
	if(tl_stats) getrusage(RUSAGE_SELF, &tr_debut);
	NFG *n;
	NFG_trans *t1 ,*t2;
	int i = 0;
	for(n=head->next;n!=tail;n=n->next){
		if(!test_is_contain(n->current,all_GF_components)){
		t1 = n->trans->next;
		while(t1!=n->trans){
			copy_the_NFG_trans(n->trans,t1);
			t2 = n->trans->next;
			while(!((t1!=t2)&&(t1->point==t2->point)
				&&test_is_contain(t2->condition,t1->condition)
				&&(test_is_contain(t1->final,t2->final)
				||(n->incoming!=t1->point->incoming)
				||(in_the_set(bad_nfg_scc,n->incoming))
				))){
				t2 = t2->next;
			}
			if(t2!=n->trans){
				/*printf("\n********************in simplify delete it \n");*/
				NFG_trans *free = t1->next;
				t1->point = free->point;
				copy_the_set(t1->condition,free->condition);
				copy_the_set(t1->final,free->final);
				t1->next = free->next;
				/*transition--;*/
				if(free==n->trans){
					n->trans = t1;
				}
				free_nfg_trans(free,0);
				i++;
			}
			else{
				t1 = t1->next;
			}
		}
	}
	}
	printf("simplified %d transitions \n",i);
	if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "simplify the GBAs' transitions: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);

	}
}
/**********************************************************************************
 * function:  generate the NFG's transform
 **********************************************************************************/
CF_trans *build_NFGs_trans(int *table,int *num){
	int i,j,start = 1;
	int number = -1;
	num = 0;
	CF_trans *result = (CF_trans*)0;
	for(i = 0; i < the_set_size; i++){
	    for(j = 0; j < mode; j++){
	    	 if(table[i] & (1 << j)){
	    		 number = mode * i + j;
	    		 num++;
	    		 if(!start){
	    			result = and_cf_form(result,copy_the_CF_trans(cf_form[number]));
	    		 }else{
	    			 result = copy_the_CF_trans(cf_form[number]);
	    		 }
	    		 number = 0;
	    		 start = 0;
	    	 }
	    }
	}
	if(number == -1){
		num = -1;
		result = cf_form[0];
	}

	return result;
}
/**********************************************************************************
 * function:  test if the state is equivalent with someone
 **********************************************************************************/
int same_NFG_trans(NFG_trans *left,NFG_trans *right){
	if((left->point!=right->point)||!test_same_sets(left->condition,right->condition)){
		return 0;
	}
	if(test_same_sets(left->final,right->final)){
		return 1;
	}

	return 0;
}
int is_equal_with(NFG *a,NFG*b){
	NFG_trans *left,*right;

	for(left=a->trans->next;left!=a->trans;left=left->next){
		copy_the_NFG_trans(b->trans,left);
		right = b->trans->next;
		while(!same_NFG_trans(left,right)){
			right = right->next;
		}
		if(right==b->trans){
			return 0;
		}
	}
	for(right=b->trans->next;right!=b->trans;right=right->next){
		copy_the_NFG_trans(a->trans,right);
		left = a->trans->next;
		while(!same_NFG_trans(right,left)){
			left = left->next;
		}
		if(left==a->trans){
			return 0;
		}
	}
	return 1;
}
/**********************************************************************************
 * function:  list the elements of current set
 **********************************************************************************/
int *list_c_set(int *current){
	int *list;
	int i,j;
	/*int number = -1;*/
	int size = 1;
	for(i = 0; i < the_set_size; i++){
	    for(j = 0; j < mode; j++){
	    	 if(current[i] & (1 << j)){
	    		 /*number = mode * i + j;*/
	    		 size++;
	    	 }
	    }
	}
	if(size==1){
		list = (int *)tl_emalloc((size+1)*sizeof(int));
		list[0] = size+1;
		list[1] = 0;
	}else {
		list = (int *)tl_emalloc(size*sizeof(int));
		list[0] = size;
		size = 1;
		for(i = 0; i < the_set_size; i++){
			for(j = 0; j < mode; j++){
				if(current[i] & (1 << j)){
					/*number = mode * i + j;*/
					list[size++] = mode * i + j;
				}
			}
		}
	}
	return list;
}
/**********************************************************************************
 * function:  create new NFG or point to the existing one
 **********************************************************************************/
NFG *find_NFG(NFG *n,int *point){
	if(compute_directly) return n;
	if(test_same_sets(n->current,point)){
		/*printf("\n===========is self\n");*/
		return n;
	}
	NFG *new_NFG;
	new_NFG = NFG_stack->next;
	NFG_stack->current = point;
	while(!test_same_sets(new_NFG->current,point)){
		new_NFG = new_NFG->next;
	}
	if(new_NFG!=NFG_stack){
		/*printf("\n===========is stack\n");*/
		return new_NFG;
	}
	new_NFG = head->next;
	tail->current = point;
	while(!test_same_sets(new_NFG->current,point)){
		new_NFG = new_NFG->next;
	}
	if(new_NFG!=tail){
		/*printf("\n===========is list\n");*/
		return new_NFG;
	}
	new_NFG = NFG_remove->next;
	NFG_remove->current = point;
	while(!test_same_sets(new_NFG->current,point)){
		new_NFG = new_NFG->next;
	}
	if(new_NFG!=NFG_remove){
		/*printf("\n===========not list\n");*/
		return new_NFG;
	}
	/*printf("\n=============need to create\n");*/
	new_NFG = (NFG*)tl_emalloc(sizeof(NFG));
	new_NFG->current = create_the_set();
	copy_the_set(new_NFG->current,point);
	/*new_NFG->final = (int *)0;*/
	/*
	new_NFG->final = create_the_set();
	clear_the_set(new_NFG->final);
	*/

	/*Node *current = print_the_node(new_NFG->current);
	printf("*********create the node's current is :\n");
	dump(current);
	printf("\n");*/
	new_NFG->trans = emalloc_NFG_trans();
	new_NFG->trans->next = new_NFG->trans;
	new_NFG->incoming = 0;
	new_NFG->next = NFG_stack->next;
	NFG_stack->next = new_NFG;
	return new_NFG;
}

/***********************************************************************************\
|* function:  test if the element in the set                                       *|
\***********************************************************************************/
int is_in_final(int *set,int element){

	return 0;
}
/***********************************************************************************\
|* function:  test if the final value is i                                         *|
\***********************************************************************************/
int is_the_final(CF_trans *trans,int i){
	int inside;
	CF_trans *t;
	if(!in_the_set(trans->point,i)){
		return 1;
	}
	/*inside = in_the_set(trans->point,i);
	rem_the_set(trans->point,i);
	for(t=cf_form[i];t;t=t->next){
		if(test_is_contain(t->condition,trans->condition)
			&&test_is_contain(t->point,trans->point)){
			add_the_set(trans->point,i);
			return 1;
		}
	}
	add_the_set(trans->point,i);*/
	return 0;
}
/***********************************************************************************\
|* function:  create the GF trans                                                  *|
\***********************************************************************************/
CF_trans *create_GF_trans(int i){
	CF_trans *GF_trans = emalloc_CF_trans();
	clear_the_set(GF_trans->point);
	add_the_set(GF_trans->point,i);
	clear_the_set(GF_trans->condition);
	return GF_trans;
}

/***********************************************************************************\
|* function:  generate the NFGs of the CF normal form                              *|
\***********************************************************************************/
void build_graph(NFG *newNFG){
	NFG *test_one;
	/*int num = 0;*/
	/*CF_trans *mk_trans = build_NFGs_trans(newNFG->current,&num);*/

	CF_trans *trans1;
	NFG_trans *the_one = (NFG_trans*)0;
	CF_list *cf_list = (CF_list*)tl_emalloc(sizeof(CF_list));
	cf_list->trans = emalloc_CF_trans();
	clear_the_set(cf_list->trans->point);
	clear_the_set(cf_list->trans->condition);
	cf_list->trans->next = cf_list->trans;
	cf_list->trans_list = cf_list->trans;
	cf_list->trans_list->next = cf_list->trans;
	cf_list->pre = cf_list;
	cf_list->next = cf_list;
	CF_list *each_one;
	int *list = list_c_set(newNFG->current);


	/*printf("\nthe current state's set:");
	print_the_set(newNFG->current);
	printf("\n");*/

	if(test_is_contain(newNFG->current,all_GF_components)){
		compute_directly = 1;
		post_pone = 0;
	}else{
		compute_directly = 0;
		/*test if the state contain the GFx*/
		if(!test_intersect(newNFG->current,GF_form)){
			if(!test_intersect(newNFG->current,FG_form)){
				post_pone = 2;
			}else{
				post_pone = 1;
			}

		}else if(!test_is_contain(newNFG->current,FG_form)&&!test_intersect(newNFG->current,FG_form)){
			post_pone = 1;
		}
		else{
			post_pone = 0;
		}
	}
	/*printf("******the compute_directly==%d\n",compute_directly);
	printf("******the post_pone==%d\n",post_pone);*/
	int i;
	for(i=1;i<list[0];i++){
		CF_list *one = (CF_list*)tl_emalloc(sizeof(CF_list));
		one->cf_num = list[i];
		if(post_pone==1&&(in_the_set(GF_form,list[i])||in_the_set(FG_form,list[i]))){
			one->trans_list = create_GF_trans(list[i]);
			one->trans = merge_CF_trans(cf_list->next->trans,one->trans_list);
		}
		else if(post_pone==2&&in_the_set(GF_form,list[i])){
			one->trans_list = create_GF_trans(list[i]);
			one->trans = merge_CF_trans(cf_list->next->trans,one->trans_list);
		}else{
			one->trans_list = node_to_CF_form(list[i]);
			one->trans = merge_CF_trans(cf_list->next->trans,one->trans_list);
		}

		one->next = cf_list->next;
		one->pre = cf_list;
		one->next->pre = one;
		one->pre->next = one;
	}



	while(1){
		each_one = cf_list->next;
		trans1 = each_one->trans;
		if(trans1){

			clear_the_set(fin);
			int in;
			for(in=0;in<final_table_ID;in++){
				if(is_the_final(trans1,final_table[in])){
					add_the_set(fin,final_table[in]);
				}
			}

			/*printf("the transition point is:(");
			print_the_set(trans1->point);
			printf(")\n");
			printf("the fin:(");
			print_the_set(fin);
			printf(")\n");*/


			/*printf("the transitino1 of cf: ");
			Node *condition1 = print_the_node(trans1->condition);
			dump(condition1);
			printf("->");
			print_the_set(trans1->point);
			printf("(");
			print_the_set(fin);
			printf(")\n");*/


			/*judge the state is GF_components or else*/


			if(compute_directly){
				NFG_trans *new_trans = emalloc_NFG_trans();
				copy_the_set(new_trans->condition,trans1->condition);
				new_trans->point = find_NFG(newNFG,trans1->point);
				new_trans->point->incoming++;
				copy_the_set(new_trans->final,fin);
				new_trans->next = newNFG->trans->next;
				newNFG->trans->next = new_trans;
			}else{

			for(the_one = newNFG->trans->next;the_one!=newNFG->trans;){
				/*
				printf("the transition in the state:");
				Node *condition = print_the_node(the_one->condition);
				dump(condition);
				printf("->");
				print_the_set(the_one->point->current);
				printf("(");
				print_the_set(the_one->final);
				printf(")\n");
				*/

				if(test_is_contain(the_one->point->current,trans1->point)
					&&test_is_contain(the_one->condition,trans1->condition)
					&&test_same_sets(the_one->final,fin)){
					/*printf("---------------------not add in \n");*/
					break;
				}else if(test_is_contain(trans1->point,the_one->point->current)
						&&test_is_contain(trans1->condition,the_one->condition)
						&&test_same_sets(the_one->final,fin)){
					/*printf("********************delete the transition \n");*/
					NFG_trans *free = the_one->next;
					the_one->point->incoming--;
					the_one->point = free->point;
					copy_the_set(the_one->condition,free->condition);
					copy_the_set(the_one->final,free->final);
					the_one->next = free->next;
					if(free == newNFG->trans){
						newNFG->trans = the_one;
					}
					free_nfg_trans(free,0);
				}else{
					the_one = the_one->next;
				}
			}
			if(the_one==newNFG->trans){
				NFG_trans *new_trans = emalloc_NFG_trans();
				copy_the_set(new_trans->condition,trans1->condition);
				new_trans->point = find_NFG(newNFG,trans1->point);
				new_trans->point->incoming++;
				copy_the_set(new_trans->final,fin);
				new_trans->next = newNFG->trans->next;
				newNFG->trans->next = new_trans;
				/*
				printf("in the make transition:\n");
				printf("the fin set is :");
				print_the_set(fin);
				printf("\n");
				Node *point = print_the_node(new_trans->point->current);
				Node *condition = print_the_node(new_trans->condition);
				printf("the transition is:   ");
				dump(condition);
				printf("->");
				print_the_set(new_trans->point->current);
				printf("(");
				print_the_set(new_trans->final);
				printf(")\n");
				*/
			}
			}
		}

		while(each_one->trans_list->next==(CF_trans*)0){
			each_one = each_one->next;
		}
		if(each_one==cf_list){
			break;
		}
		each_one->trans_list = each_one->trans_list->next;
		do_merge_CF_trans(&each_one->trans,each_one->next->trans,each_one->trans_list);
		each_one = each_one->pre;
		while(each_one!=cf_list){
			if(post_pone==1&&(in_the_set(GF_form,each_one->cf_num)||in_the_set(FG_form,each_one->cf_num))){
				each_one->trans_list = create_GF_trans(each_one->cf_num);
			}else if(post_pone==2&&in_the_set(GF_form,each_one->cf_num)){
				each_one->trans_list = create_GF_trans(each_one->cf_num);
			}else{
				each_one->trans_list = cf_form[each_one->cf_num];
			}
			do_merge_CF_trans(&each_one->trans,each_one->next->trans,each_one->trans_list);
			each_one = each_one->pre;

		}
	}
	/*release the memory*/
	tfree(list);
	while(cf_list->next!=cf_list){
		CF_list *remov = cf_list->next;
		cf_list->next = remov->next;
		free_cf_trans(remov->trans,0);
		tfree(remov);
	}
	free_cf_trans(cf_list->trans,0);
	tfree(cf_list);
	/*free_all_CF_trans();*/

	if(!compute_directly){
		/*printf("****woqu\n");*/
    if(newNFG->trans->next==newNFG->trans){/*newNFG has no transition*/
    	free_nfg_trans_list(newNFG->trans->next,newNFG->trans,1);
    	newNFG->trans = (NFG_trans*)0;
    	newNFG->pre = (NFG*)0;
		newNFG->next = NFG_remove->next;
		NFG_remove->next = newNFG;
		NFG *rm;
		for(rm=NFG_remove->next;rm!=NFG_remove;rm=rm->next){
			if(rm->pre==newNFG){
				rm->pre = (NFG*)0;
			}
		}
		return ;
    }
	/*test if the state is equivalent with someone in the head list*/
	tail->trans = newNFG->trans;
	/*tail->final = newNFG->final;*/
	test_one = head->next;
	while(!is_equal_with(test_one,newNFG)){
		test_one = test_one->next;
	}
	if(test_one!=tail){  /*newNFG is redundant*/
		/*printf("\n************************delete the state\n");*/
		free_nfg_trans_list(newNFG->trans->next,newNFG->trans,1);
		newNFG->trans = (NFG_trans*)0;
		newNFG->pre = test_one;
		newNFG->next = NFG_remove->next;
		NFG_remove->next = newNFG;
		NFG *rm;
		for(rm=NFG_remove->next;rm!=NFG_remove;rm=rm->next){
			if(rm->pre==newNFG){
				rm->pre = newNFG->pre;
			}
		}
		return ;
	}
	}
	/*add the NFG in the list*/
	newNFG->pre = cursor;
	cursor->next = newNFG;
	newNFG->next = tail;
	tail->pre = newNFG;
	cursor = newNFG;
	/*
	Node *current = print_the_node(newNFG->current);
	printf("*****************************\n the current state is: \n");
	dump(current);
	printf("**set is :(");
	print_the_set(newNFG->current);
	printf(")");
	NFG_trans *trans;
	for(trans=newNFG->trans->next;trans!=newNFG->trans;trans=trans->next){
		Node *condition = print_the_node(trans->condition);
		printf("\n");
		dump(condition);
		printf("->");
		print_the_set(trans->point->current);
		printf("(");
		print_the_set(trans->final);
		printf(")");
	}
	printf("\n\n");
	*/


}

/**********************************************************************************
 * function:  print the graph generate the dot file
 **********************************************************************************/
void print_the_graph(){
	if(tl_stats) getrusage(RUSAGE_SELF, &tr_debut);
	if((dot=fopen("graph.dot","w"))==NULL){
	    printf("can't open file");
	}
	fprintf(dot,"%s","digraph finite_state_machine {\n");
	NFG *one;
	/*printf("\n print the graph:\n");*/
    for(one=head->next;one!=tail;one=one->next){
    	Node *current = print_the_node(one->current);
    	NFG_trans *trans;
    	graph_ID++;
    	/*
    	if(one->final){
    		printf("\n the state \n");
    		dump(current);
    		printf("\n the final set:\n");
    		print_the_set(one->final);
    		printf("\n");
    	}
    	*/
		/*printf("\n the current state is: \n");
		dump(current);
		printf("**set is :(");
		print_the_set(one->current);
		printf(")");*/
    	for(trans=one->trans->next;trans!=one->trans;trans=trans->next){
    		/*printf("\n current's set is :\n");
    		print_the_set(one->current);
    		printf("\n");
			printf("condition's set is :\n");
			print_the_set(trans->condition);
			printf("\n");
			printf("next state's set is :\n");
			print_the_set(trans->point->current);
			printf("\n");*/

    		Node *point = print_the_node(trans->point->current);
    		Node *condition = print_the_node(trans->condition);

    		/*printf("\n");
    		dump(condition);
    		printf("->");
    		print_the_set(trans->point->current);
    		printf("(");
    		print_the_set(trans->final);
    		printf(")");*/


			printf("\n the current state is: \n");
			dump(current);
			printf("\nset is :");
			print_the_set(one->current);
			printf("\n the next state is :\n");
			dump(point);
			printf("\nset is :");
			print_the_set(trans->point->current);
			printf("\n transform condition is \n");
			dump(condition);
			printf("\n final set:");
			print_the_set(trans->final);
			printf("\n");

    		transition++;
			fprintf(dot,"%c",34);
			mydump(current);
			fprintf(dot,"%c",34);

			fprintf(dot," -> ");

			fprintf(dot,"%c",34);
			mydump(point);
			fprintf(dot,"%c",34);

			fprintf(dot," [ label = ");
			fprintf(dot,"%c",34);
			mydump(condition);
			fprintf(dot,"%c",34);
			fprintf(dot," ];\n");
    	}

    }
	fprintf(dot,"%s","}\n");
	fclose(dot);
	if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "print the GBAs: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);

	}
}
/**********************************************************************************
 * function:  add the element in the set
 **********************************************************************************/
void add_and_element(int *initial,Node *p){
	if(p->ntyp!=AND){
		return ;
	}
	if(p->ntyp==AND){
		if(p->lft->ntyp!=AND){
			add_the_set(initial,index_of_table(p->lft));
		}
		if(p->rgt->ntyp!=AND){
			add_the_set(initial,index_of_table(p->rgt));
		}
		if(p->lft->ntyp==AND){
			add_and_element(initial,p->lft);

		}
		if(p->rgt->ntyp==AND){
			add_and_element(initial,p->rgt);
		}
	}


}
/**********************************************************************************
 * function:  initialize the beginning node
 **********************************************************************************/
int *inital_begin_node(Node *p){
	int *initial = create_the_set();
	clear_the_set(initial);
	add_and_element(initial,p);
	return initial;
}
void intial_begin_or_node(Node *p){
	if(p->ntyp!=OR) return ;
	if(p->ntyp==OR){
		if(p->lft->ntyp!=OR && p->rgt->ntyp==OR){
			NFG *lft_newNFG = (NFG*)tl_emalloc(sizeof(NFG));
			lft_newNFG->incoming = 1;
			lft_newNFG->trans = emalloc_NFG_trans();
			lft_newNFG->trans->next = lft_newNFG->trans;
			lft_newNFG->current = create_the_set();
			clear_the_set(lft_newNFG->current);
			if(p->ntyp==AND){
				lft_newNFG->current = inital_begin_node(p->lft);

			}else{
				add_the_set(lft_newNFG->current,index_of_table(p->lft));
			}
			lft_newNFG->next = NFG_stack->next;
			NFG_stack->next = lft_newNFG;

			NFG *rgt_newNFG = (NFG*)tl_emalloc(sizeof(NFG));
			rgt_newNFG->incoming = 1;
			rgt_newNFG->trans = emalloc_NFG_trans();
			rgt_newNFG->trans->next = rgt_newNFG->trans;
			rgt_newNFG->current = create_the_set();
			clear_the_set(rgt_newNFG->current);
			if(p->ntyp==AND){
				rgt_newNFG->current = inital_begin_node(p->rgt);

			}else{
				add_the_set(rgt_newNFG->current,index_of_table(p->rgt));
			}
			rgt_newNFG->next = NFG_stack->next;
			NFG_stack->next = rgt_newNFG;

			intial_begin_or_node(p->rgt);
		}
		if(p->rgt->ntyp!=OR&&p->lft->ntyp==OR){
			NFG *lft_newNFG = (NFG*)tl_emalloc(sizeof(NFG));
			lft_newNFG->incoming = 1;
			lft_newNFG->trans = emalloc_NFG_trans();
			lft_newNFG->trans->next = lft_newNFG->trans;
			lft_newNFG->current = create_the_set();
			clear_the_set(lft_newNFG->current);
			if(p->ntyp==AND){
				lft_newNFG->current = inital_begin_node(p->lft);

			}else{
				add_the_set(lft_newNFG->current,index_of_table(p->lft));
			}
			lft_newNFG->next = NFG_stack->next;
			NFG_stack->next = lft_newNFG;

			NFG *rgt_newNFG = (NFG*)tl_emalloc(sizeof(NFG));
			rgt_newNFG->incoming = 1;
			rgt_newNFG->trans = emalloc_NFG_trans();
			rgt_newNFG->trans->next = rgt_newNFG->trans;
			rgt_newNFG->current = create_the_set();
			clear_the_set(rgt_newNFG->current);
			if(p->ntyp==AND){
				rgt_newNFG->current = inital_begin_node(p->rgt);

			}else{
				add_the_set(rgt_newNFG->current,index_of_table(p->rgt));
			}
			rgt_newNFG->next = NFG_stack->next;
			NFG_stack->next = rgt_newNFG;
			intial_begin_or_node(p->lft);
		}
		if(p->lft->ntyp!=OR&&p->rgt->ntyp!=OR){
			NFG *lft_newNFG = (NFG*)tl_emalloc(sizeof(NFG));
			lft_newNFG->incoming = 1;
			lft_newNFG->trans = emalloc_NFG_trans();
			lft_newNFG->trans->next = lft_newNFG->trans;
			lft_newNFG->current = create_the_set();
			clear_the_set(lft_newNFG->current);
			if(p->ntyp==AND){
				lft_newNFG->current = inital_begin_node(p->lft);

			}else{
				add_the_set(lft_newNFG->current,index_of_table(p->lft));
			}
			lft_newNFG->next = NFG_stack->next;
			NFG_stack->next = lft_newNFG;

			NFG *rgt_newNFG = (NFG*)tl_emalloc(sizeof(NFG));
			rgt_newNFG->incoming = 1;
			rgt_newNFG->trans = emalloc_NFG_trans();
			rgt_newNFG->trans->next = rgt_newNFG->trans;
			rgt_newNFG->current = create_the_set();
			clear_the_set(rgt_newNFG->current);
			if(p->ntyp==AND){
				rgt_newNFG->current = inital_begin_node(p->rgt);

			}else{
				add_the_set(rgt_newNFG->current,index_of_table(p->rgt));
			}
			rgt_newNFG->next = NFG_stack->next;
			NFG_stack->next = rgt_newNFG;

		}
		if(p->rgt->ntyp==OR&&p->lft->ntyp==OR){
			NFG *lft_newNFG = (NFG*)tl_emalloc(sizeof(NFG));
			lft_newNFG->incoming = 1;
			lft_newNFG->trans = emalloc_NFG_trans();
			lft_newNFG->trans->next = lft_newNFG->trans;
			lft_newNFG->current = create_the_set();
			clear_the_set(lft_newNFG->current);
			if(p->ntyp==AND){
				lft_newNFG->current = inital_begin_node(p->lft);

			}else{
				add_the_set(lft_newNFG->current,index_of_table(p->lft));
			}
			lft_newNFG->next = NFG_stack->next;
			NFG_stack->next = lft_newNFG;

			NFG *rgt_newNFG = (NFG*)tl_emalloc(sizeof(NFG));
			rgt_newNFG->incoming = 1;
			rgt_newNFG->trans = emalloc_NFG_trans();
			rgt_newNFG->trans->next = rgt_newNFG->trans;
			rgt_newNFG->current = create_the_set();
			clear_the_set(rgt_newNFG->current);
			if(p->ntyp==AND){
				rgt_newNFG->current = inital_begin_node(p->rgt);

			}else{
				add_the_set(rgt_newNFG->current,index_of_table(p->rgt));
			}
			rgt_newNFG->next = NFG_stack->next;
			NFG_stack->next = rgt_newNFG;
			intial_begin_or_node(p->lft);
			intial_begin_or_node(p->rgt);
		}
	}
}
/**********************************************************************************
 * function:  generate all the NFGs of the CF normal form
 **********************************************************************************/
void build_all_graph(Node *p,Node *ptr){
	if(tl_stats) getrusage(RUSAGE_SELF, &tr_debut);
	/*
	if(p->ntyp==OR&&!check(p)){
		intial_begin_or_node(p);
		printf("*****nimeia\n");
	}else{*/
	NFG *newNFG = (NFG*)tl_emalloc(sizeof(NFG));
	newNFG->incoming = 1;
	newNFG->trans = emalloc_NFG_trans();
	newNFG->trans->next = newNFG->trans;
	newNFG->current = create_the_set();
	clear_the_set(newNFG->current);
	/*newNFG->final = (int *)0;*/
	/*
	newNFG->final = create_the_set();
	clear_the_set(newNFG->final);
	*/

	/*newNFG->current = inital_begin_node(p);
	printf("the first node set is :\n");
	print_the_set(newNFG->current);*/


	if(p->ntyp==AND){
		newNFG->current = inital_begin_node(p);

	}else{
		add_the_set(newNFG->current,index_of_table(p));
	}


	newNFG->next = NFG_stack->next;
	NFG_stack->next = newNFG;
/*	}*/

	while(NFG_stack->next!=NFG_stack){
		NFG *deal = NFG_stack->next;
		NFG_stack->next = NFG_stack->next->next;
		if(deal->incoming==0){
			/*Node *curr = print_the_node(deal->current);
			printf("not yet make trans ,the Node is\n");
			dump(curr);
			printf("\n");*/

			free_NFG(deal);
			continue;
		}
		build_graph(deal);
	}
	if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "Building the GBAs: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);
	}


}
/**********************************************************************************
 * function:  generate the GBA of the CF normal form  (the NFG here is  GBA)
 **********************************************************************************/
void mk_NFGs(Node *p){
	if(tl_stats) getrusage(RUSAGE_SELF, &tr_debut);
	/*Node *one1 = dupnode(p);*/
	Node *ptr = NF_normal(p);
	node_num = calculate_nodetree_szie(p)+2;
	node_table = (Node **) tl_emalloc((node_num) * sizeof(Node *));
	final_table = (int*) tl_emalloc((node_num) * sizeof(int));
	cf_form = (CF_trans**)tl_emalloc((node_num)*sizeof(CF_trans*));
	/*is_decomposed = (int**)tl_emalloc((10*node_num)*sizeof(int*));*/
	/*all_graph = (NFG**)tl_emalloc((10*node_num*node_num)*sizeof(NFG*));*/
	head = (NFG*)tl_emalloc(sizeof(NFG));
	tail = (NFG*)tl_emalloc(sizeof(NFG));
	NFG_stack = (NFG*)tl_emalloc(sizeof(NFG));
	NFG_remove = (NFG*)tl_emalloc(sizeof(NFG));
	NFG_stack->next = NFG_stack;
	NFG_remove->next = NFG_remove;
	cursor = head;
	head->next = tail;
	tail->pre = head;
	the_set_size = node_num / (8 * sizeof(int)) + 1;
	fin = create_the_set();
	the_final_set = create_the_set();
	GF_form = create_the_set();
	FG_form = create_the_set();
	all_GF_components = create_the_set();
	/*printf("all the node is:\n");*/
	initial_node_table(p);
	/*printf("\n");
	printf("the node tree number is %d\n",node_num);
	printf("the set size number is %d\n",the_set_size);*/

	/*printf("initial state:\n");
	dump(p);
	printf("\n");*/
	/*printf("the C-F normal form is:\n");
	dump(ptr);
	printf("\n");*/

	/*if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "initial_node_table: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);

	}*/

	initial_CF_form();

	/*if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "initial_CF_form: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);

	}/*


    /*printf("\n the final set is :\n");*/
	int i;
	for(i=0;i<final_table_ID;i++){
		/*printf("%d    ",final_table[i]);*/
		add_the_set(the_final_set,final_table[i]);
	}
	/*printf("\n");*/

	int j;
	for(j=0;j<node_table_ID;j++){
		/*printf("%d    ",final_table[i]);*/
		cf_form[j] = (CF_trans*)0;
	}

	/*printf("the GF_components set:");
	print_the_set(all_GF_components);
	printf("\n");
	printf("the GF_form set:");
	print_the_set(GF_form);
	printf("\n");*/

	printf("the node number is %d\n",node_table_ID-1);
	if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "preparation: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);

	}

	build_all_graph(p,ptr);



	retarget_all_NFG_trans();

	nfg_scc();

	simplify_all_NFG_trans();



	free_all_CF_trans();
	tfree(cf_form);

	if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "free the memory: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);

	}


	if(tl_print_ba){
		print_the_graph();
	}

	/*printf("\n the GBA SCC is %d\n",nfg_scc_ID);*/

	/**printf("\n all the transition is : %d\n",transition);
	printf("\n all the state number is : %d\n",graph_ID);*/
	/*printf("\n the final table number is :%d\n",final_table_ID);*/
	/*printf("call the NF numbers is %d\n ",NF_num);*/
	/*printf("\n all the state number is : %d\n",has_decomposed);*/
	/*printf("\n at last all the graph 's number is : %d\n",true_graph_ID);*/


	/*
	if(tl_stats) {
	    getrusage(RUSAGE_SELF, &tr_fin);
	    timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
	    fprintf(tl_out, "simplify the GBAs: %i.%06is\n",
			t_diff.tv_sec, t_diff.tv_usec);

	}*/


}



/* Written by Jun Song, Xi'an, China                                   */
/* Copyright (c) 2014  Jun Song                                        */
#include "ltl_nf_ba.h"
/***********************************************************
 * global variables
 ***********************************************************/
extern NFG *head, *tail;
extern int final_table_ID;
extern int *final_table;
CF_bstate *cf_bstack,*cf_bremove,*cf_bhead,*cf_btail,*cf_bcursor;
int cf_bstate_num=0,cf_btrans_num=0;
extern FILE *dot;
extern int tl_print_ba;

/*************************************************************************************
 * function:free the memory of the state
 *************************************************************************************/
void free_cf_bstate(CF_bstate *the_one){
	free_cf_btrans(the_one->trans->next,the_one->trans,1);
	tfree(the_one);
}
/*************************************************************************************
 * function:copy the cf_btrans
 *************************************************************************************/
void copy_cf_btrans(CF_btrans *to,CF_btrans *from){
	to->point = from->point;
	copy_the_set(to->condition,from->condition);
}
/*************************************************************************************
 * function: compute the "final" value
 *************************************************************************************/
int final_value(int *final_set,int final){
	if((final!=final_table_ID)&&in_the_set(final_set,final_table[final])){
		return final_value(final_set,final+1);
	}
	return final;
}
/**********************************************************************************
 * function:  simplify the transition of the automata
 **********************************************************************************/
void simplify_the_cf_btrans(){
	CF_bstate *the_state;
	CF_btrans *t1,*t2;
	for(the_state=cf_bhead->next;the_state!=cf_btail;the_state=the_state->next){
		for(t1=the_state->trans->next;t1!=the_state->trans;){
			t2 = the_state->trans->next;
			copy_cf_btrans(the_state->trans,t1);
			while((t1==t2||t1->point!=t2->point)
					||!test_is_contain(t2->condition,t1->condition)){
				t2 = t2->next;
			}
			if(t2!=the_state->trans){
				CF_btrans *free = t1->next;
				/*t1->point->incoming--;*/
				t1->point = free->point;
				copy_the_set(t1->condition,free->condition);
				t1->next = free->next;
				if(free==the_state->trans){
					the_state->trans = t1;
				}
				free_cf_btrans(free,(CF_btrans*)0,0);

			}else{
				t1 = t1->next;
			}
		}
	}
}
/**********************************************************************************
 * function:  delete the redundant state and reposition the transition
 **********************************************************************************/
void retarget_all_cf_btrans(){
	CF_bstate *the_state;
	CF_btrans *t1;
	for(the_state=cf_bhead->next;the_state!=cf_btail;the_state=the_state->next){
		for(t1=the_state->trans->next;t1!=the_state->trans;t1=t1->next){
			if(!t1->point->trans){
				t1->point = t1->point->pre;
			}

		}
	}
	while(cf_bremove->next!=cf_bremove){
		the_state = cf_bremove->next;
		cf_bremove->next = cf_bremove->next->next;
		tfree(the_state);
	}

}
/**********************************************************************************
 * function:  judge the two state is equivalent
 **********************************************************************************/
int same_cf_btrans(CF_btrans *left,CF_btrans *right){
	return (left->point==right->point)&&test_same_sets(left->condition,right->condition);
}
int is_cf_bstate_equal(CF_bstate *a,CF_bstate *b){
	CF_btrans *left,*right;
	/*add the new judgment condition*/
	if(a->final!=b->final){
		return 0;
	}
	for(left=a->trans->next;left!=a->trans;left=left->next){
		copy_cf_btrans(b->trans,left);
		right = b->trans->next;
		while(!same_cf_btrans(left,right)){
			right = right->next;
		}
		if(right==b->trans){
			return 0;
		}
	}
	for(right=b->trans->next;right!=b->trans;right=right->next){
		copy_cf_btrans(a->trans,right);
		left = a->trans->next;
		while(!same_cf_btrans(left,right)){
			left = left->next;
		}
		if(left==a->trans){
			return 0;
		}
	}
	return 1;
}
/*************************************************************************************
 * function:print the graph of the buchi automata
 *************************************************************************************/
void print_the_cf_bstate(){
	if((dot=fopen("ba.dot","w"))==NULL){
	    printf("can't open file");
	}
	fprintf(dot,"%s","digraph finite_state_machine {\n");
	CF_bstate *one;
		/*printf("\n print the graph:\n");*/
	for(one=cf_bhead->next;one!=cf_btail;one=one->next){
		CF_btrans *trans;
		Node *current = print_the_node(one->nfg_state->current);
	    /*NFG_trans *trans;
	    	/*
	    	if(one->final){
	    		printf("\n the state \n");
	    		dump(current);
	    		printf("\n the final set:\n");
	    		print_the_set(one->final);
	    		printf("\n");
	    	}
	    	*/
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
	    	Node *point = print_the_node(trans->point->nfg_state->current);
	    	Node *condition = print_the_node(trans->condition);

				/*printf("\n the current state is: \n");
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
				*/
	    	cf_btrans_num++;
			fprintf(dot,"%c",34);
			mydump(current);
			fprintf(dot,"#");
			fprintf(dot,"%d",one->final);
			fprintf(dot,"%c",34);

			fprintf(dot," -> ");

			fprintf(dot,"%c",34);
			mydump(point);
			fprintf(dot,"#");
			fprintf(dot,"%d",trans->point->final);
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
}
/*************************************************************************************
 * function:create a new state or point to the existing one
 *************************************************************************************/
CF_bstate *find_cf_bstate(NFG *n,int fin,CF_bstate *one){
	if(one->nfg_state==n&&one->final==fin){
		return one;
	}
	CF_bstate *new_state;

	new_state = cf_bstack->next;
	cf_bstack->final = fin;
	cf_bstack->nfg_state = n;
	while(!(new_state->final==fin)||!(new_state->nfg_state==n)){
		new_state = new_state->next;
	}
	if(new_state!=cf_bstack){
		return new_state;
	}

	new_state = cf_bhead->next;
	cf_btail->final = fin;
	cf_btail->nfg_state = n;
	while(!(new_state->final==fin)||!(new_state->nfg_state==n)){
		new_state = new_state->next;
	}
	if(new_state!=cf_btail){
		return new_state;
	}

	new_state = cf_bremove->next;
	cf_bremove->final = fin;
	cf_bremove->nfg_state = n;
	while(!(new_state->final==fin)||!(new_state->nfg_state==n)){
		new_state = new_state->next;
	}
	if(new_state!=cf_bremove){
		return new_state;
	}

	/*printf("\n *************************build new b state\n");*/
	new_state = (CF_bstate*)tl_emalloc(sizeof(CF_bstate));
	new_state->incoming = 0;
	new_state->nfg_state = n;
	/*Node *current = print_the_node(n->current);
	printf("the new state is :\n");
	dump(current);
	printf("#%d",fin);
	printf("\n");*/
	new_state->final = fin;
	new_state->trans = emalloc_cf_btrans();
	new_state->trans->next = new_state->trans;
	new_state->next = cf_bstack->next;
	cf_bstack->next = new_state;
	return new_state;
}
/*************************************************************************************
 * function:generate the buchi automata
 *************************************************************************************/
void build_cf_btrans(CF_bstate *the_state){
	/*printf("begin to make transition\n");*/
	NFG_trans *t;
	CF_btrans *the_trans;
	CF_bstate *test_one;
	if(the_state->nfg_state->trans){
		for(t=the_state->nfg_state->trans->next;t!=the_state->nfg_state->trans;t=t->next){
			/*int fin;*/
			/*printf("the transition's final is :\n");
			print_the_set(t->final);
			printf("\n the state's final is %d\n",the_state->final);*/
			int fin = final_value(t->final,(the_state->final==final_table_ID ? 0 : the_state->final));
			/*printf("\n in the build transition the fin==%d\n",fin);*/
			CF_bstate *to = find_cf_bstate(t->point,fin,the_state);
			for(the_trans=the_state->trans->next;the_trans!=the_state->trans;){
				if((the_trans->point==to)&&test_is_contain(the_trans->condition,t->condition)){
					/*printf("\n********not add the cf_btrans\n");*/
					break;
				}
				else if ((the_trans->point==to)&&test_is_contain(t->condition,the_trans->condition)){
					/*the_trans is redundant*/
					/*printf("\n*********delete the cf_btrans\n");*/
					CF_btrans * free = the_trans->next;
					the_trans->point->incoming--;
					the_trans->point = free->point;
					copy_the_set(the_trans->condition,free->condition);
					the_trans->next = free->next;
					if(free==the_state->trans){
						the_state->trans = the_trans;
					}
					free_cf_btrans(free,(CF_btrans*)0,0);
				}else{
					the_trans=the_trans->next;
				}
			}
			if(the_trans==the_state->trans){
				CF_btrans *new_trans = emalloc_cf_btrans();
				new_trans->point = to;
				new_trans->point->incoming++;
				copy_the_set(new_trans->condition,t->condition);
				new_trans->next = the_state->trans->next;
				the_state->trans->next = new_trans;
			}
		}
	}
	if(the_state->trans==the_state->trans->next){
		free_cf_btrans(the_state->trans->next,the_state->trans,1);
		the_state->trans = (CF_btrans*)0;
		the_state->pre = (CF_bstate*)0;
		the_state->next = cf_bremove->next;
		cf_bremove->next = the_state;
		CF_bstate *rm;
		for(rm=cf_bremove->next;rm!=cf_bremove;rm=rm->next){
			if(rm->pre==the_state){
				rm->pre = (CF_bstate*)0;
			}
			return ;
		}
	}
	cf_btail->trans = the_state->trans;
	cf_btail->final = the_state->final;
	test_one = cf_bhead->next;
	while(!is_cf_bstate_equal(test_one,the_state)){
		test_one = test_one->next;
	}
	if(test_one!=cf_btail){
		/*Node *current1 = print_the_node(test_one->nfg_state->current);
		printf("the same state is :\n");
		dump(current1);
		printf("#%d",test_one->final);
		printf("\n");

		printf("************delete the state\n");
		Node *current = print_the_node(the_state->nfg_state->current);
		printf("the delete state is :\n");
		dump(current);
		printf("#%d",the_state->final);
		printf("\n");*/
		free_cf_btrans(the_state->trans->next,the_state->trans,1);
		the_state->trans = (CF_btrans*)0;
		the_state->pre = test_one;
		the_state->next = cf_bremove->next;
		cf_bremove->next = the_state;
		CF_bstate *rm;
		for(rm=cf_bremove->next;rm!=cf_bremove;rm=rm->next){
			if(rm->pre==the_state){
				rm->pre = the_state->pre;
			}
		}
	}else{
		the_state->pre = cf_bcursor;
		cf_bcursor->next = the_state;
		the_state->next = cf_btail;
		cf_btail->pre = the_state;
		cf_bcursor = the_state;
		/*Node *current2 = print_the_node(the_state->nfg_state->current);
		printf("------------add state in the list is :\n");
		dump(current2);
		printf("#%d",the_state->final);
		printf("\n");*/
		cf_bstate_num++;
		/*printf("**************add on state:\n");*/
	}
}
/*************************************************************************************
 * function:generate the BA from the GBA
 *************************************************************************************/
void mk_cf_ba(){
	/*printf("-----------initial the automata\n");*/
	cf_bhead = (CF_bstate*)tl_emalloc(sizeof(CF_bstate));
	cf_btail = (CF_bstate*)tl_emalloc(sizeof(CF_bstate));
	cf_bstack = (CF_bstate*)tl_emalloc(sizeof(CF_bstate));
	cf_bremove = (CF_bstate*)tl_emalloc(sizeof(CF_bstate));
	cf_bcursor = cf_bhead;
	cf_bstack->next = cf_bstack;
	cf_bremove->next = cf_bremove;

	CF_bstate *init = (CF_bstate*)tl_emalloc(sizeof(CF_bstate));
	init->incoming = 1;
	init->final = 0;
	init->nfg_state = (NFG*)0;
	init->trans = emalloc_cf_btrans();
	init->trans->next = init->trans;
	cf_bhead->next = init;
	init->pre = cf_bhead;
	tail->pre = init;
	init->next = cf_btail;
	cf_bcursor = init;
	cf_bstate_num++;

	init->nfg_state = head->next;
	NFG_trans *t;
	CF_btrans *the_trans;
	for(t=init->nfg_state->trans->next;t!=init->nfg_state->trans;t=t->next){
		/*int fin;*/
		/*printf("\n the transition's final is :\n");
		print_the_set(t->final);
		printf("\n");*/
		int fin = final_value(t->final,0);
		/*printf("\n in the initial the fin==%d\n",fin);*/

		CF_bstate *to = find_cf_bstate(t->point,fin,init);
		/*printf("*******sucess one time\n");*/
		for(the_trans=init->trans->next;the_trans!=init->trans;the_trans=the_trans->next){
			if((the_trans->point==to)&&test_is_contain(the_trans->condition,t->condition)){
				break;
			}
			else if ((the_trans->point==to)&&test_is_contain(t->condition,the_trans->condition)){
				/*the_trans is redundant*/
				CF_btrans * free = the_trans->next;
				the_trans->point->incoming--;
				the_trans->point = free->point;
				copy_the_set(the_trans->condition,free->condition);
				the_trans->next = free->next;
				if(free==init->trans){
					init->trans = the_trans;
				}
				free_cf_btrans(free,(CF_btrans*)0,0);
			}
		}
		if(the_trans==init->trans){
			CF_btrans *new_trans = emalloc_cf_btrans();
			new_trans->point = to;
			new_trans->point->incoming++;
			copy_the_set(new_trans->condition,t->condition);
			new_trans->next = init->trans->next;
			init->trans->next = new_trans;

		}

	}
	while(cf_bstack->next!=cf_bstack){
		CF_bstate *deal = cf_bstack->next;
		cf_bstack->next = cf_bstack->next->next;
		if(deal->incoming==0){
			free_cf_bstate(deal);
			continue;
		}
		build_cf_btrans(deal);
	}
	retarget_all_cf_btrans();
	if(tl_print_ba) {print_the_cf_bstate();}
	simplify_the_cf_btrans();
	/*printf("\n the buchi automata state's number is %d\n",cf_bstate_num);
	printf("the buchi automata transition's number is %d\n",cf_btrans_num);*/
}

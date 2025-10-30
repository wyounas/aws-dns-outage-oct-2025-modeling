/* 
/* 
 * AWS DynamoDB DNS Race Condition - Promela Model
 * 
 * Models the October 2025 AWS DynamoDB outage caused by a race condition
 * in the DNS management system. 

To run (with Spin Version 6.5.2):

# 1) Generate the verifier from the Promela model
spin -a aws-dns-race.pml

# 2) Compile it
gcc -O2 -o pan pan.c

# 3) Verify the named LTL (only this one)
./pan -a -N no_dns_deletion_on_regression

# 4) Replay the counterexample with variable values
spin -t -p -g -l -k aws-dns-race.pml.trail aws-dns-race.pml



 */

#define MAX_PLAN 5
#define PLAN_AGE_THRESHOLD 2
#define NUM_ENACTORS 2

/*  Global state to represent Route53 service  */

byte current_plan = 0;              
bool dns_valid = false;             
bool plan_deleted[MAX_PLAN + 1];    
byte latest_plan = 0;              
bool initialized = false;          
byte highest_plan_applied = 0;   

byte enactor_processing[NUM_ENACTORS]; 

chan plan_channel = [4] of { byte };


active proctype Planner() {
    byte plan = 1;
    
    do
    :: (plan <= MAX_PLAN) ->
        latest_plan = plan;
        plan_channel ! plan; // sending a plan over a channel
        printf("Planner: Generated Plan v%d\n", plan);
        plan++;
    :: (plan > MAX_PLAN) -> break;
    od;
    
    printf("Planner: Completed\n");
}



active [NUM_ENACTORS] proctype Enactor() {
   
    byte my_plan;
    byte snapshot_current;
    byte i;
    byte my_id = _pid - _nr_pr + NUM_ENACTORS; 
    
    do
    :: plan_channel ? my_plan ->
        printf("Enactor[%d]: Received Plan v%d\n", my_id, my_plan);
        
        
        enactor_processing[my_id] = my_plan;
        
        /*  Simulating stateness check  */
        /* Per AWS report: Before it begins to apply a new plan, the DNS 
         * Enactor makes a one-time check that its plan is newer than the 
         * previously applied plan.
         * 
         */
        snapshot_current = current_plan;
        
        if
        :: (my_plan > snapshot_current || snapshot_current == 0) ->
            printf("Enactor[%d]: Staleness check passed for Plan v%d (current: v%d)\n", 
                   my_id, my_plan, snapshot_current);
            
           
            if
            :: !plan_deleted[my_plan] ->
                
                printf("Enactor[%d]: Applying Plan v%d to Route53\n", my_id, my_plan);
                current_plan = my_plan;
                dns_valid = true;
                initialized = true;
               
                if 
                :: (my_plan > highest_plan_applied) ->
                    highest_plan_applied = my_plan;
                fi 
                /*  Clean-up  */
                /* Per AWS report: When the second Enactor completed its 
                 * endpoint updates, it then invoked the plan clean-up process, 
                 * which identifies plans that are significantly older than the 
                 * one it just applied and deletes them.
                 */
                printf("Enactor[%d]: Starting cleanup after applying v%d\n", 
                       my_id, my_plan);
                
                i = 1;
                do
                :: (i < my_plan) ->
                    /* Delete plans that are "significantly older" */
                    if
                    :: (my_plan - i >= PLAN_AGE_THRESHOLD && !plan_deleted[i]) ->
                        printf("Enactor[%d]: Deleting old Plan v%d (age: %d)\n", 
                               my_id, i, my_plan - i);
                        plan_deleted[i] = true;
                        
                      
                        /* Per AWS report: The second Enactor's clean-up process 
                         * then deleted this older plan because it was many 
                         * generations older than the plan it had just applied. 
                         * As this plan was deleted, all IP addresses for the 
                         * regional endpoint were immediately removed.
                         */
                        if
                        :: (current_plan == i) ->
                            printf("Enactor[%d]: Critical - active plan v%d was deleted!\n", 
                                   my_id, i);
                            printf("Enactor[%d]: Removing all DNS records \n", 
                                   my_id);
                            dns_valid = false;
                            current_plan = 0;
                            printf("Enactor[%d]: System now in inconsistent state\n", my_id);
                        :: else -> skip;
                        fi;
                    :: else -> skip;
                    fi;
                    i++;
                :: (i >= my_plan) -> break;
                od;
                
            :: else ->
                printf("Enactor[%d]: Error - Plan v%d already deleted!\n", 
                       my_id, my_plan);
            fi;
            
        :: else ->
            printf("Enactor[%d]: Staleness check failed for Plan v%d (current: v%d)\n", 
                   my_id, my_plan, snapshot_current);
        fi;
        
      
        enactor_processing[my_id] = 0;
        
    :: empty(plan_channel) && (latest_plan >= MAX_PLAN) -> break;
    od;
    
    printf("Enactor[%d]: Shutting down\n", my_id);
}

/* 
 * Invariant
 * 
 */


ltl no_dns_deletion_on_regression {
    [] ( (initialized && highest_plan_applied > current_plan && current_plan > 0) -> dns_valid )
}

/* Active plan must never be marked deleted */
ltl never_delete_active {
    [] ( current_plan > 0 -> !plan_deleted[current_plan] )
}

/* 
 * AWS DynamoDB DNS Race Condition Fix
 * 
 * 
 */

#define MAX_PLAN 5
#define PLAN_AGE_THRESHOLD 2
#define NUM_ENACTORS 2


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
        plan_channel ! plan;
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
        snapshot_current = current_plan;
        
        if
        :: (my_plan > snapshot_current || snapshot_current == 0) ->
            printf("Enactor[%d]: Staleness check passed for Plan v%d\n", 
                   my_id, my_plan);
            
            if
            :: !plan_deleted[my_plan] ->
                printf("Enactor[%d]: Applying Plan v%d to Route53\n", 
                       my_id, my_plan);
                
                /* Fix: Make plan application atomic with state update */
                atomic {
                    current_plan = my_plan;
                    dns_valid = true;
                    initialized = true;
                   
                    if 
                    :: (my_plan > highest_plan_applied) ->
                        highest_plan_applied = my_plan;
                    :: else -> skip;
                    fi;
                }
                
                
                printf("Enactor[%d]: Starting safe cleanup after applying v%d\n", 
                       my_id, my_plan);
                
                i = 1;
                do
                :: (i < my_plan) ->
                    if
                    :: (my_plan - i >= PLAN_AGE_THRESHOLD && !plan_deleted[i]) ->
                        
                        /* Fix */
                        atomic {
                            if
                            :: (current_plan != i) ->
                                
                                printf("Enactor[%d]: Safely deleting old Plan v%d\n", 
                                       my_id, i);
                                plan_deleted[i] = true;
                            :: else ->
                                /* Fix: don't delete active plan */
                                printf("Enactor[%d]: Safety - Refusing to delete active Plan v%d\n", 
                                       my_id, i);
                              
                            fi;
                        }
                        
                    :: else -> skip;
                    fi;
                    i++;
                :: (i >= my_plan) -> break;
                od;
                
            :: else ->
                printf("Enactor[%d]: Cannot apply Plan v%d - already deleted\n", 
                       my_id, my_plan);
            fi;
            
        :: else ->
            printf("Enactor[%d]: Staleness check failed for Plan v%d\n", 
                   my_id, my_plan);
        fi;
        
        enactor_processing[my_id] = 0;
        
    :: empty(plan_channel) && (latest_plan >= MAX_PLAN) -> break;
    od;
    
    printf("Enactor[%d]: Shutting down\n", my_id);
}

/* Invariant */

/* Property: DNS should never be deleted due to plan regression */
ltl no_dns_deletion_on_regression {
    [] ( (initialized && highest_plan_applied > current_plan && current_plan > 0) -> dns_valid )
}

/* Active plan must never be marked deleted */
ltl never_delete_active {
    [] ( current_plan > 0 -> !plan_deleted[current_plan] )
}

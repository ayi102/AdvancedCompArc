/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
//                                                                             //
// This file is distributed as part of the Championship Branch Prediction      //
// workshop held in conjunction with ISCA'2014.                                //
// Everyone is granted permission to copy, modify, and/or re-distribute        //
// this software.                                                              //
// Please contact Moinuddin Qureshi <moin@gatech.edu> if you have any questions//
//                                                                             //
/////////////////////////////////////////////////////////////////////////////////

// --- DO NOT EDIT THIS FILE --- DO NOT EDIT THIS FILE --- DO NOT EDIT THIS FILE ---
// IMPORTANT NOTE: Changing anything in here will violate the competition rules.



#include "utils.h"
#include "tracer.h"
#include "predictor.h"
#include "profiler.h"
#include <vector>
// usage: predictor <trace>

int main(int argc, char* argv[]){
  
  if (argc != 2) {
    printf("usage: %s <trace>\n", argv[0]);
    exit(-1);
  }

  ///////////////////////////////////////////////
  // Init variables
  ///////////////////////////////////////////////
    
    CBP_TRACER *tracer = new CBP_TRACER(argv[1]);
    PREDICTOR  *brpred = new PREDICTOR();
    CBP_TRACE_RECORD *trace = new CBP_TRACE_RECORD();
    UINT64     numMispred =0;  
    profile stats (1);
    UINT64     numUncondBr = 0;
    UINT64     numDirCalls = 0;
    UINT64     numRet = 0;
  ///////////////////////////////////////////////
  // read each trace recod, simulate until done
  ///////////////////////////////////////////////
      while (tracer->GetNextRecord(trace)) {

	if(trace->opType >= OPTYPE_CALL_DIRECT && trace->opType <= OPTYPE_BRANCH_COND) {
 
          // count unconditional branches
          if(trace->opType == OPTYPE_BRANCH_UNCOND)
             numUncondBr++;
          else if(trace->opType == OPTYPE_CALL_DIRECT)
             numDirCalls++;
          else if(trace->opType == OPTYPE_RET)
             numRet++;
          // count executions for each branch
          stats.count_exe(trace->PC,0);
          stats.count_loops(trace->PC,trace->branchTaken,trace->opType);
          stats.store_targets(trace->PC,trace->branchTarget);
          stats.track_calls(trace->PC,trace->opType, trace->branchTarget);
	  bool predDir = brpred->GetPrediction(trace->PC);

	  brpred->UpdatePredictor(trace->PC, trace->branchTaken, 
				  predDir, trace->branchTarget);
        
	  if(predDir != trace->branchTaken){
	    numMispred++; // update mispred stats
	  }
	  
	}
        // for predictors that want to track all insts
	else{
	  brpred->TrackOtherInst(trace->PC, trace->opType, trace->branchTarget);
	}
      
      }

    ///////////////////////////////////////////
    //print_stats
    ///////////////////////////////////////////

      /*printf("\n");
      printf("\nNUM_INSTRUCTIONS     \t : %10llu",   tracer->GetNumInst());
      printf("\nTOTAL_BRANCHES       \t : %10llu",   (tracer->GetNumCondBranch() + numUncondBr + numDirCalls + numRet));
      printf("\nNUM_CONDITIONAL_BR   \t : %10llu",   tracer->GetNumCondBranch());
      printf("\nNUM_UNCONDITIONAL_BR \t : %10llu",   numUncondBr);
      printf("\nNUM_DIRECT_BR        \t : %10llu",   numDirCalls);
      printf("\nNUM_RET_BR           \t : %10llu",   numRet);*/
      stats.write_raw_data();
      stats.write_dead();
      stats.write_glacial();
      stats.write_loops();
      stats.write_top_ten();
      stats.write_matches();
      stats.call_history_stats();
      stats.write_stats(numUncondBr,tracer->GetNumCondBranch(), numDirCalls, numRet);
      printf("\n\n");
}




#include<map>
#include<vector>
#include<fstream>
#include<string>
#include<iostream>
#include<climits>
#include<iomanip>
#include "utils.h"
#include "tracer.h"
using namespace std;

class profile {

   map<UINT32,vector<UINT32> > profiler;
   map<UINT32,vector<UINT32> > reduced_dead;
   map<UINT32,vector<UINT32> > reduced_glacial;
   map<UINT32,vector<UINT32> > reduced_loops;
   map<UINT32,vector<UINT32> > glacial_branches;
   map<UINT32,vector<UINT32> > dead_branches;
   map<UINT32,vector<UINT32> > loop_branches;
   map<UINT32,vector<UINT32> > matches;
   map<UINT32,vector<UINT32> > branch_targets;
   map<UINT32,vector<UINT32> > call_history;
   map<UINT32,vector<UINT32> > count_rets;
   int NUM_OF_COUNTERS;
   int global_counter;
   UINT32 curr_key;
   int HISTORY_SIZE;

   // for dead branch stats
   double count_takens;
   double count_not_takens;
   double count_taken_exe;
   double count_ntaken_exe;
   double count_cond_takens;
   double count_cond_nottakens;
   // for glacial branch stats
   double count_glacial;
   // for loop branch stats
   double count_patterns;
   double count_irreg;

   public:
   profile(int);
   void count_exe(UINT32,int);
   void count_loops(UINT32,bool,int);
   void track_calls(UINT32,int,UINT32);
   void write_matches();
   void write_raw_data();
   void write_top_ten();
   void write_stats(int,int,int,int);
   void write_dead();
   void write_glacial();
   void write_loops();
   void call_history_stats();
   void store_targets(UINT32, UINT32);
   void write_map(map<UINT32,vector<UINT32> > &source, string file_name, unsigned int length);
};

profile::profile(int size) {
   NUM_OF_COUNTERS = size;
   global_counter = 0;
   curr_key = 0;

   // init glacial stats
   count_glacial = 0.0;
  
   // init dead stats
   count_takens = 0.0;
   count_not_takens = 0.0 ;
   count_taken_exe = 0.0;
   count_ntaken_exe = 0.0;
   count_cond_takens = 0.0;
   count_cond_nottakens = 0.0;

   // init loop stats
   count_patterns = 0.0;
   count_irreg = 0.0;
   HISTORY_SIZE = 100;
}
/* prints the raw data on all branches
 * includes: PC of Branch : Execution Count, Branch Type, History...
 */
void profile::write_raw_data(){

   profile::write_map(profiler,"1_raw_stats.txt", HISTORY_SIZE);
}
/* prints the top 10 most executed branches */
void profile::write_top_ten(){
   map<UINT32,vector<UINT32> > top_ten;
   bool not_in_top = false;
   int top_ten_count = 0;

   // capture top ten branches
   for(map<UINT32,vector<UINT32> >::iterator iter_top = profiler.begin(); iter_top != profiler.end();++iter_top){
      UINT32 key_top = (*iter_top).first;
      vector<UINT32> tempVecTop = (*iter_top).second;
      for(map<UINT32,vector<UINT32> >::iterator iter_bottom = profiler.begin(); iter_bottom != profiler.end();++iter_bottom){
         vector<UINT32> tempVecBot = (*iter_bottom).second;

         if(tempVecTop[0] < tempVecBot[0])
            top_ten_count++;
         if(top_ten_count  > 9)
            not_in_top = true;
      }
      if(!not_in_top)
         top_ten[key_top].push_back(tempVecTop[0]);
      not_in_top = false;
      top_ten_count = 0;
   }
   // capture top ten branches pattern
   for(map<UINT32,vector<UINT32> >::iterator iter = top_ten.begin(); iter != top_ten.end(); ++iter){
      UINT32 key = (*iter).first;
      for(unsigned j = 2; j < profiler[key].size(); j++){
         top_ten[key].push_back(profiler[key][j]);
      }
   }
   profile::write_map(top_ten,"6_top_ten_branches.txt",HISTORY_SIZE);
}
/* identifies dead branches, writes dead branches to a file, filters raw data of dead branches and writes to a file*/
void profile::write_dead(){
   bool all_not_takens = true;
   bool all_takens = false;
    
   for(map<UINT32,vector<UINT32> >::iterator iter = profiler.begin(); iter != profiler.end();++iter){
      vector<UINT32> tempVec = (*iter).second;
      UINT32 key = (*iter).first;

       if(profiler[key].size() == 3 && profiler[key][0] == profiler[key][2]){
         all_takens = true;
         count_takens = count_takens + 1.0;
         count_taken_exe += profiler[key][0];

          // track the branch identity
         if(profiler[key][1] == OPTYPE_BRANCH_COND)
            count_cond_takens = count_cond_takens + 1.0;
       }
       else{
         for(unsigned i = 2; i < tempVec.size() && all_not_takens; i++){
            if(tempVec[i] != 0)
               all_not_takens = false;
         }
         if(all_not_takens)
         {
            count_not_takens = count_not_takens + 1.0;
            count_ntaken_exe += profiler[key][0];

            // tracke the branch identity
            if(profiler[key][1] == OPTYPE_BRANCH_COND)
               count_cond_nottakens++;
         }
       }

       if(!all_takens && !all_not_takens){
         for(unsigned i = 0; i < profiler[key].size();i++){
            reduced_dead[key].push_back(profiler[key][i]);
         }
      }
      else{
         for(unsigned i = 0; i < profiler[key].size();i++){
            dead_branches[key].push_back(profiler[key][i]);
         }
      }
      all_not_takens = true;
      all_takens = false;
   }
   profile::write_map(reduced_dead,"2_reduced_dead.txt",HISTORY_SIZE);
   profile::write_map(dead_branches,"4_dead.txt",HISTORY_SIZE);
}
/* writes overall stats on traces, should be run last*/
void profile::write_stats(int uncond_tot, int cond_tot, int dir_calls, int ret_calls){
   ofstream file;
   file.open("9_branch_stats.txt");

   bool verified = true;

   // for branch execution verification
   double total_count = 0.0;
   UINT32 branch_count = 0;
   double count_cond = 0.0;
   double count_uncond = 0.0;
   double count_calls = 0.0;
   double count_ret = 0.0;

   // branch totals
   double cond = 0.0;
   double uncond = 0.0;
   double calls = 0.0;
   double ret = 0.0;

   for(map<UINT32,vector<UINT32> >::iterator iter = profiler.begin(); iter != profiler.end();++iter){
      vector<UINT32> tempVec = (*iter).second;
      UINT32 key = (*iter).first;
      total_count += profiler[key][0];
   
      /*-------------------Verification--------------------------*/
      // count the branch history
      for(unsigned i = 2; i < tempVec.size(); i++){
         if(tempVec[i] == NOT_TAKEN)
            branch_count++;
         else
            branch_count += tempVec[i];
      }
      // compare branch total stats
      if(branch_count != profiler[key][0])
         verified = false;

      // get totals for uncond, cond, ret, and call branches to verify
      if(profiler[key][1] == OPTYPE_BRANCH_UNCOND)
      {
         count_uncond += branch_count;
         uncond++;
      }
      else if(profiler[key][1] == OPTYPE_BRANCH_COND)
      {
         count_cond += branch_count;
         cond++;
      }
      else if(profiler[key][1] == OPTYPE_RET)
      {
         count_ret += branch_count;
         ret++;
      }
      else
      {
         count_calls += branch_count;
         calls++;
      }

      // reset all_takens flag and count
      branch_count = 0;
   }

   // print stats on branch targets
   profile::write_map(branch_targets, "7_branch_targets.txt",INT_MAX);
   profile::write_map(call_history, "8_call_history.txt",INT_MAX);
   profile::write_map(count_rets, "13_rets_per_call_history.txt",INT_MAX);

   // print stats on all takens and not takens
   file << "-----------------Total Branches------------------" << "\n";
   file << "Total Branches                  : " << profiler.size() << "\n";
   file << "Total Unconditional Branches    : " << uncond << "\n";
   file << "Total Conditional   Branches    : " << cond << "\n";
   file << "Total Direct Call   Branches    : " << calls << "\n";
   file << "Total Return        Branches    : " << ret << "\n";
   file << "--------------Total Branch Executions------------" << "\n";
   file << "Total Branch Executions         : " << std::setprecision(10) << total_count << "\n";
   file << "Total Unconditional Branch Exes : " << count_uncond << "\n";
   file << "Total Conditional   Branch Exes : " << count_cond << "\n";
   file << "Total Direct Call   Branch Exes : " << count_calls << "\n";
   file << "Total Return        Branch Exes : " << count_ret << "\n";
   file << "-----------------Branch Break Down---------------" << "\n";
   file << "% Unconditional Branch Exes     : " << count_uncond*100/total_count << "\n";
   file << "% Conditional   Branch Exes     : " << count_cond*100/total_count << "\n";
   file << "% Direct Call   Branch Exes     : " << count_calls*100/total_count << "\n";
   file << "% Return        Branch Exes     : " << count_ret*100/total_count << "\n";
   file << "-------------Dead Branch Break Down--------------" << "\n";
   file << "Branches All Taken              : " << count_takens << "\n";
   file << "Branches All Not Takens         : " << count_not_takens << "\n";
   file << "# of Unonditional All Taken     : " << uncond << "\n";
   file << "# of Conditional All Taken      : " << count_cond_takens << "\n";
   file << "# of Direct Call All Taken      : " << calls << "\n";
   file << "# of Retrun Call All Taken      : " << ret << "\n";
   file << "# of Conditional All Not Takens : " << count_cond_nottakens << "\n";
   file << "% All Taken Branches            : " << 100*count_takens/profiler.size() << "\n";
   file << "% All Not Takens Branches       : " << 100*count_not_takens/profiler.size() << "\n";
   file << "--------Dead Branch Execution Break Down---------" << "\n";
   file << "# of Taken Executions           : " << std::setprecision(10) << count_taken_exe << "\n";
   file << "# of Not Taken Executions       : " << count_ntaken_exe << "\n";
   file << "% of Dead Executions            : " << (count_taken_exe + count_ntaken_exe) * 100/total_count << "\n";
   file << "---------General Branch Break Down-----" << "\n";
   file << "# of Dead           Branches    : " << dead_branches.size() << "\n";
   file << "# of Glacial        Branches    : " << glacial_branches.size() << "\n";
   file << "# of Pot. Loop Branches         : " << loop_branches.size() << "\n";
   file << "# of Pot. Irregular Branches    : " << reduced_loops.size() << "\n";
   file << "% of Dead Branches              : " <<  100*(count_takens+count_not_takens)/profiler.size() << "\n";
   file << "% of Glacial Branches           : " << static_cast<double>(glacial_branches.size())*100/profiler.size() << "\n";
   file << "% of Loop    Branches           : " << static_cast<double>(loop_branches.size())*100/profiler.size() << "\n";
   file << "% of Irregular Branches         : " << static_cast<double>(reduced_loops.size())*100/profiler.size() << "\n";
   file << "% of Dead Executions            : " << (count_taken_exe + count_ntaken_exe) * 100/total_count << "\n";
   file << "% of Glacial Branch Execution   : " << count_glacial*100/total_count << "\n";
   file << "% of Loop Executions            : " << count_patterns*100/total_count << "\n";
   file << "% of Irregular Executions       : " << count_irreg*100/total_count << "\n";
   file << "----------Call History Stats---------" << "\n";
   file << "# of Full Call Histories        : " << call_history.size() << "\n";
   file << "-------------VERIFICATION-------------" << "\n";
   
   if(total_count == (uncond_tot+cond_tot+dir_calls+ret_calls))
      file << "Total Branch Count Verified" << "\n";
   else
      file << "Total Branch Count Incorrect" << "\n";

   if(verified)
      file << "Per-Branch Count Verified" << "\n";
   else
      file << "Per Branch Count Incorrect" << "\n";

   if(uncond_tot == count_uncond && cond_tot == count_cond && count_ret == ret_calls && count_calls == dir_calls)
      file << "Op Type Counts Verified" << "\n";
   else
      file << "Op Type Counts Incorrect" << "\n";

   file.close();
}
/* this method is called as the trace runs, and it counts the number of exectuions
 * of each branch*/
void profile::count_exe(UINT32 key, int index){
   if(profiler.find(key) != profiler.end())
   {
      profiler[key][index]++;
   }
   else
   {
      profiler[key].push_back(TAKEN);
   }
}
/* generates the branch history, accumulates takens and writes out not takens*/
void profile::count_loops(UINT32 key, bool branchTaken, int opType){
   // init for first loop
   if(profiler[key].size() == 1)
   {
      // store previous branch result
      if(branchTaken == NOT_TAKEN)
      { 
         profiler[key].push_back(opType);
         profiler[key].push_back(NOT_TAKEN);
      }
      else
      {
         profiler[key].push_back(opType);
         profiler[key].push_back(TAKEN);
      }
   }
   else
   {
      if(branchTaken == NOT_TAKEN)
      {
         profiler[key].push_back(NOT_TAKEN);
      }
      else
      {
         int index = profiler[key].size();
         if(profiler[key][index-1] > 0)
            profiler[key][index - 1]++;
         else
            profiler[key].push_back(1);
      }
         
   }
}
/* this method tracks direct calls to capture function calls and their histories*/
void profile::track_calls(UINT32 key,int opType, UINT32 branchTarget){
   if(global_counter == 0 && opType == OPTYPE_CALL_DIRECT){
      // identify the top most level function call
      curr_key = key;
   }
   if(curr_key != 0){
      if(opType == OPTYPE_CALL_DIRECT)
         global_counter++;
      // ***Can addjust what is recorded by the profiler to see what the keys of all  direct calls are
      // ***May throw off the counts compared by the profiler in call_history_stats
      // ***Change all push_backs to push_back(opType) to get an accurate count from the profiler
      if(opType == OPTYPE_RET)
         call_history[curr_key].push_back(opType);
      else if (opType == OPTYPE_CALL_DIRECT)
         call_history[curr_key].push_back(opType);
      else
         call_history[curr_key].push_back(opType);
      if(opType == OPTYPE_RET){
         global_counter--;
      }
      // ensure histories outside of a call are not recorded
      if(global_counter == 0)
         curr_key = 0;
   } 
}
/* counts direct calls and return calls of every potential function call history*/
void profile::call_history_stats(){
  for(map<UINT32,vector<UINT32> >::iterator iter = call_history.begin(); iter != call_history.end();++iter){
     UINT32 key = (*iter).first;
     vector<UINT32> tempVec = (*iter).second;

     // init map to count returns per history
     count_rets[key].push_back(0);
     count_rets[key].push_back(0);
     for(unsigned i = 0; i < tempVec.size(); i++){
        if(call_history[key][i] == OPTYPE_RET)
           count_rets[key][0]++;
        else if(call_history[key][i] == OPTYPE_CALL_DIRECT)
           count_rets[key][1]++;
     } 
  } 
}
/* trackes the target branches of every branches */
void profile::store_targets(UINT32 key, UINT32 branchTarget){
   if(branch_targets[key].empty())
   {
      branch_targets[key].push_back(branchTarget);
   }
   else
   {
      if(branch_targets[key].back() != branchTarget)
         branch_targets[key].push_back(branchTarget);
   }
}
/* finds branches with matching execution histories */
void profile::write_matches(){

   bool matched = true;

   for(map<UINT32,vector<UINT32> >::iterator top_iter = reduced_dead.begin(); top_iter != reduced_dead.end();++top_iter){
      UINT32 top_key = (*top_iter).first;
      vector<UINT32> topVec = (*top_iter).second;
      for(map<UINT32,vector<UINT32> >::iterator bot_iter = reduced_dead.begin(); bot_iter != reduced_dead.end();++bot_iter){
         UINT32 bot_key = (*bot_iter).first;
         vector<UINT32> botVec = (*bot_iter).second;
         if(top_key != bot_key && topVec.size() == botVec.size()){
            for(unsigned i = 0; i < botVec.size(); i++){
               if(reduced_dead[top_key][i] != reduced_dead[bot_key][i])
                  matched = false;
            }
            if(matched){
               matches[top_key].push_back(bot_key);
            }
            matched = true;
         }
      }
   }
   profile::write_map(matches,"10_matches.txt",HISTORY_SIZE);
}
/* finds branches with very predictable branch histories*/
void profile::write_loops(){
   int cnt = 2;
   bool found_pattern;
   bool quite_loop = false;
   bool takens = false;
   int iterations;

   for(map<UINT32,vector<UINT32> >::iterator iter = reduced_glacial.begin(); iter != reduced_glacial.end();++iter){
      vector<UINT32> tempVec = (*iter).second;
      UINT32 key = (*iter).first;
      
      if(tempVec.size()/2 > 12)
         iterations = 30;
      else
         iterations = tempVec.size()/2;
      while(cnt <= iterations && tempVec.size() > 3 && !quite_loop){
         vector<UINT32> pattern;
         found_pattern = true;
         // grab a pattern set
         for(int j = 2; j < cnt+2; j++){
            pattern.push_back(reduced_glacial[key][j]);
         }
         // iterate through the reduced profiler to find a pattern
         for(int k = 0; k < cnt && found_pattern; k++){
            if(pattern[k] != reduced_glacial[key][cnt+k+2])
               found_pattern = false;
            else if(pattern[k] > 0)
               takens = true;
         }

         if(found_pattern && takens)
            quite_loop = true;

         cnt++;
      }
      if(found_pattern && takens){
         for(unsigned i = 0; i < tempVec.size(); i++){
            loop_branches[key].push_back(tempVec[i]);
         }
         count_patterns += loop_branches[key][0];
      }
      else{
         for(unsigned i = 0; i < tempVec.size(); i++)
         {
            reduced_loops[key].push_back(tempVec[i]);
         }
         count_irreg += reduced_loops[key][0];
      }
      takens = false;
      quite_loop = false;
      cnt = 2;
   }
   
   profile::write_map(loop_branches,"11_loops.txt",HISTORY_SIZE);
   profile::write_map(reduced_loops,"12_reduced_loops.txt",HISTORY_SIZE);
}
/* finds branches with glacial histories*/
void profile::write_glacial(){

   double cnt_notaken = 0;
   double cnt_taken = 0;
   double glacial_yield = 0;
   double thresh_hold = 85.0;

   for(map<UINT32,vector<UINT32> >::iterator iter = reduced_dead.begin(); iter != reduced_dead.end();++iter){
     vector<UINT32> tempVec = (*iter).second;
     UINT32 key = (*iter).first;
     // find any glacial branches
     // experiment with the threash hold
     for(unsigned i = 2; i < tempVec.size(); i++){
        if(tempVec[i] == NOT_TAKEN)
           cnt_notaken++;
        else
           cnt_taken += tempVec[i];
     }
     glacial_yield = cnt_notaken*100/(cnt_taken+cnt_notaken);
     // store a profile without the glacial branches
     if(glacial_yield < thresh_hold)
     {
        for(unsigned i = 0; i < tempVec.size(); i++)
           reduced_glacial[key].push_back(tempVec[i]);
     }
     else
     {
        for(unsigned i = 0; i < tempVec.size(); i++)
           glacial_branches[key].push_back(tempVec[i]);

        count_glacial = (count_glacial+cnt_notaken+cnt_taken);
     }
     cnt_taken = 0;
     cnt_notaken = 0;
   }

   profile::write_map(reduced_glacial,"3_reduced_glacial.txt",HISTORY_SIZE);
   profile::write_map(glacial_branches,"5_glacial.txt",HISTORY_SIZE);
}
/* prints out a map of vectors */
void profile::write_map(map<UINT32,vector<UINT32> > &source, string file_name, unsigned int length){
   ofstream file;

   file.open(file_name.c_str());
   
   for(map<UINT32,vector<UINT32> >::iterator iter = source.begin(); iter != source.end();++iter){
     vector<UINT32> tempVec = (*iter).second;
     UINT32 key = (*iter).first;
     file << key << " : ";
     for(unsigned i = 0; i < tempVec.size() && i < length; i++){
        //if(i != 1)
           file << tempVec[i] << " ";
     }
     file << "\n";
   }
   file.close();
}

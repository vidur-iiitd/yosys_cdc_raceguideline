#include <stdlib.h>
#include <stdio.h>
#include <sstream>
#include <stdarg.h>
#include <algorithm>
#include <string>
#include <iostream>
#include <fstream>

//***********************************************************************************************************
//This function is similar to Backend::extra_args but used to
//print the checked guidelines or warning if any to a file 
//provided by users
void extra_args_summary(std::ofstream *&f, std::string &filename)
{
	bool bin_output = false;
	rewrite_filename(filename);
	std::ofstream *ff = new std::ofstream;
	ff->open(filename.c_str(), bin_output ? (std::ofstream::trunc | std::ofstream::binary) : std::ofstream::trunc);
	yosys_output_files.insert(filename);
	if (ff->fail()) {
		delete ff;
		log_cmd_error("Can't open output file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
	}
	f = ff;
}
//*************************************************************************************************************


int summary_race(std::map <std::string, int> &summary_race_guidelines){

    std::string filename = "summary.rpt";
    std::ofstream *f = NULL;
    std::ofstream file ;
    extra_args_summary(f, filename);

    file.open(filename.c_str());
    file << "//*****************************************************************************************" << std::endl;
    file << "//**  General format of the following files:" <<std::endl;
    file << "//**  /module name : Number_of_race_guidelines_violations" << std::endl;
    file << "//*****************************************************************************************" << std::endl;
    file << " " << std::endl;
    file << " " << std::endl;
    file << "The summary report of design check for race guidelines is mentioned below :" << std::endl;
    file << std::endl;
    for(auto itr=summary_race_guidelines.begin(); itr != summary_race_guidelines.end(); itr++)
       file << itr->first << " : " << itr->second << std::endl;
 
    file.close();
    return 0;
}
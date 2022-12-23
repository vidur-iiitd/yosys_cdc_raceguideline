#include "kernel/log.h"
#include "kernel/utils.h"
#include "kernel/binding.h"
#include "libs/sha1/sha1.h"
#include "ast.h"
#include "ast_binding.h"
#include "kernel/bitpattern.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "kernel/consteval.h"
#include "kernel/rtlil.h"
#include <stdlib.h>
#include <stdio.h>
#include <sstream>
#include <stdarg.h>
#include <algorithm>


// std::vector <std::string> string_ast_values; //used for storing the string values
// std::vector <std::string> total_args; //used for storing the type name of AST tree
// std::vector <std::string> ast_extract_info; //used for storing ast extracted data
// //std::vector <std::string> comb_latch_ff_details; // used to store latch, comb and ff, true for latch, NULL for ff, false for Combination
// //std::vector <std::string> string_details; //To check guideline number 6 
// //std::multimap <std::string, int> string_values; //Trying dictionary
// //std::multimap <std::string, std::string> string_values_update; //Trying dictionary
// std::vector <std::string> line_info; //used to store the line number details

//***********************************************************************************************************
//Different namespace as through this namespace we want to access ASTNODE or AST
YOSYS_NAMESPACE_BEGIN
using namespace AST;
using namespace AST_INTERNAL;
//***********************************************************************************************************
//Seperating different type name and required string fields
//for identifying token
//the normal string line can be consist in following format
//AST_WIRE <../capstone/race_guidelines.v:2.8-2.10> [0x56218808d5a0] str='\y1' output port=1
//this functions help us seperating above line on the basis of spaces
//We can read AST_WIRE from this
std::string splitting_token(std::string &text, const char *sep, bool long_strings)
{
	size_t pos_begin = text.find_first_not_of(sep);

	if (pos_begin == std::string::npos)
		pos_begin = text.size();

	if (long_strings && pos_begin != text.size() && text[pos_begin] == '"') {
		string sep_string = sep;
		for (size_t i = pos_begin+1; i < text.size(); i++) {
			if (text[i] == '"' && (i+1 == text.size() || sep_string.find(text[i+1]) != std::string::npos)) {
				std::string token = text.substr(pos_begin, i-pos_begin+1);
				text = text.substr(i+1);
				return token;
			}
			if (i+1 < text.size() && text[i] == '"' && text[i+1] == ';' && (i+2 == text.size() || sep_string.find(text[i+2]) != std::string::npos)) {
				std::string token = text.substr(pos_begin, i-pos_begin+1);
				text = text.substr(i+2);
				return token + ";";
			}
		}
	}

	size_t pos_end = text.find_first_of(sep, pos_begin);

	if (pos_end == std::string::npos)
		pos_end = text.size();

	std::string token = text.substr(pos_begin, pos_end-pos_begin);
	text = text.substr(pos_end);
	return token;
}

//*************************************************************************************************************
void AstNode::checking_rules_try(FILE *f, std::string indent) const
{
	if (f == NULL) {
		for (auto f : log_files)
			checking_rules_try(f, indent);
		return;
	}
	std::string type_name = type2str(type);
	//fprintf(f, "%s%s <%s>", indent.c_str(), type_name.c_str(), loc_string().c_str());
	line_info.push_back(loc_string().c_str());
	//line_number.push_back(location.first_line);
	if (!str.empty()){
		string_ast_values.push_back(str.c_str());
	}
	else
	{
		string_ast_values.push_back("NULL");
	}
	
	//***********************************************************************************
	//basically i have try to make everything and figure out type_name contains complete file which is read
	//so for starters I have converted it to a string type so that we can extract the module name
	//for extracting module name I have copied a function from kernel/register.cc
	std::string modules_check = type_name.c_str();
	std::vector<std::string> args;
	
	std::string modules_name = splitting_token(modules_check, " \t\r\n", true);

	while (!modules_name.empty()) {
		if (modules_name.back() == ';') {
			int num_semikolon = 0;
			while (!modules_name.empty() && modules_name.back() == ';')
				modules_name.resize(modules_name.size()-1), num_semikolon++;
			if (!modules_name.empty())
				args.push_back(modules_name);
			//call(design, args);
			args.clear();
		} else
			args.push_back(modules_name);
		modules_name = splitting_token(modules_check, " \t\r\n", true);
	}

	
	total_args.push_back(args[0].c_str());	

	for (auto &it : attributes) {
		it.second->checking_rules_try(f, indent + "");
	}
	

	for (size_t i = 0; i < children.size(); i++){
		children[i]->checking_rules_try(f, indent + "");
	}
	fflush(f);
}
//*************************************************************************************************************

// //*************************************************************************************************************
// //This function is actually where we are operating on always block
// //To check guidelines
// void processing_always_guidelines(std::vector <std::string> &processing_always , int index){
// 	bool flag_posedge = false;
// 	bool flag_negedge = false;
// 	bool flag_edge = false;
// 	bool flag_nonblocking = false;
// 	bool flag_blocking = false;

// 	int posedge_index;
// 	int nonblocking_index;
// 	int blocking_index;
	
// 	for(long unsigned int i=0; i<processing_always.size(); i++){
// 		//std::cout << processing_always[i] <<std::endl;
// 		if (processing_always[i] == "AST_POSEDGE"){
// 			flag_posedge = true;
// 			posedge_index = i;
// 		}
// 		if (processing_always[i] == "AST_NEGEDGE"){
// 			flag_negedge = true;
// 			//negedge_index = i;
// 		}
// 		if (processing_always[i] == "AST_EDGE"){
// 			flag_edge = true;
// 			//edge_index = i;
// 		}
// 		if (processing_always[i] == "AST_ASSIGN_LE"){
// 			flag_nonblocking = true;
// 			nonblocking_index = i;
// 			if (processing_always[i+3]== "AST_IDENTIFIER"){
// 				string_values.emplace(processing_always[i+4], index);
// 				string_values_update.emplace(processing_always[i+4], processing_always[i+5]);
// 			}
// 		}

// 		if (processing_always[i] == "AST_ASSIGN_EQ"){
// 			flag_blocking = true;	
// 			blocking_index = i;
// 			if (processing_always[i+3]== "AST_IDENTIFIER"){
// 				string_values.emplace(processing_always[i+4], index);
// 				string_values_update.emplace(processing_always[i+4], processing_always[i+5]);
// 			}
// 		}
// 	}

// 	if (((flag_posedge == true)||(flag_negedge == true)) && (flag_blocking == true)){
// 		std::cout << processing_always[(blocking_index)+2] <<std::endl;
// 		printf("Not a good practice to use blocking assignments in sequential blocks \n");
// 	}

// 	if((flag_edge==true) && (flag_nonblocking==true)){
// 		if (comb_latch_ff_details[index-1] == "FALSE"){
// 			std::cout << processing_always[(nonblocking_index)+2] <<" : ";
// 			printf("Not a good practice to use non-blocking assignments in combinational blocks \n");
// 		}
// 	}

// 	if((flag_edge==true) && (flag_blocking==true)){
// 		if (comb_latch_ff_details[index-1] == "TRUE"){
// 			std::cout << processing_always[(blocking_index)+2] <<" : ";
// 			printf("Not a good practice to use blocking assignments in sequential blocks \n");
// 		}
// 	}

// 	if((flag_posedge == true) && (flag_negedge == true)){
// 		std::cout << processing_always[(posedge_index)+2] <<" : ";
// 		printf("Not a good practice to use both positive and negative edges in same always block \n");
// 	}
	
// 	if((flag_blocking == true) && (flag_nonblocking == true)){
// 		std::cout << processing_always[(blocking_index)+2] <<" : ";
// 		printf("Not a good practice to use both blocking and non blocking assignment in same always block \n");
// 	}
// }
// //*************************************************************************************************************

//*************************************************************************************************************
//Printing all the vectors to make ensure to verify the operations
void print_vectors()
{
	long unsigned int i;
	//std::vector <std::string> ast_extract_info;
	//combining both type_name and string values
	for (i = 0; i < string_ast_values.size(); i++) {
		//std::cout << line_info[i] << "  " << total_args[i] << "  " << string_ast_values[i] << std::endl;
		ast_extract_info.push_back(total_args[i]);
		ast_extract_info.push_back(string_ast_values[i]);
		ast_extract_info.push_back(line_info[i]);
    }

	//Printing ast_extract_info
	for(i=0; i<ast_extract_info.size(); i++){
		std::cout << ast_extract_info[i] << std::endl;
	}
	//printf("The total ast_extract_info has been printed \n");

	//clearing all the vectors and map
	// dupl_elements.clear();
	// string_values.clear();
	// string_values_update.clear();
	// string_ast_values.clear(); 
	// total_args.clear();
	// comb_latch_ff_details.clear();

}
//***********************************************************************************************************


//function to check whether the posedge and negedge arriving together
void rules()
{
	//printf("We are checking for edges here \n");
	//printf("*********************************************** \n");
	//checkingforedges();
    //design_check(design);
	//printf("*********************************************** \n");
	//printf("We are checking for race guidelines here \n");
	//printf("*********************************************** \n");
	//checkingforraceguidelines();
	//printf("*********************************************** \n");
	current_ast->checking_rules_try(NULL, "    ");
	print_vectors();
}

YOSYS_NAMESPACE_END
//Ending rules program 
//*************************************************************************************************************

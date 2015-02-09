import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Scanner;


public class agent {
	String query="";
	int kbLength = 0;
	int initialMatch;
	int previousMatch=99999;
	HashMap<Integer, String> premises = new HashMap<Integer, String>();
	HashMap<Integer, String> consequences = new HashMap<Integer, String>();
	List<String> knowledgeBaseRaw = new ArrayList<String>();
	List<clause> premise = new ArrayList<clause>();
	List<clause> consequence = new ArrayList<clause>();
	List<String> queryArguments = new ArrayList<String>();
	matchedConsequences queryDetail = new matchedConsequences();
	
	List<details> premiseDetails = new ArrayList<details>();
	List<details> consequenceDetails = new ArrayList<details>();
	List<matchedConsequences> queryDetails = new ArrayList<matchedConsequences>();
	
	HashMap<Integer, List<matchedConsequences>> premisesToMatch = new HashMap<Integer, List<matchedConsequences>>();
	HashMap<Integer, matchedConsequences> consequencesToMatch = new HashMap<Integer, matchedConsequences>();
	HashMap<Integer, List<details>> premiseMap = new HashMap<Integer, List<details>>();
	
	public static void main(String[] args){
		List<String> inDocument = new ArrayList<String>();
		agent obj = new agent();
		try {
            Scanner sc = new Scanner(new File("input.txt"));
            while(sc.hasNextLine()) 
            {
               String next = sc.nextLine();
               inDocument.add(next);
            }
            sc.close();
        } 
        catch (FileNotFoundException ex) 
        {
        	System.out.println("make sure the name of the input file is input.txt and it is placed in the same directory as the .java and makefile files are");
        	return;
        }
		//printArray(inDocument);
		obj.query = inDocument.get(0);
		obj.kbLength = Integer.parseInt(inDocument.get(1));
		
		for(int i=2; i<2+obj.kbLength;i++){
			obj.knowledgeBaseRaw.add(inDocument.get(i));
		}
		
//		System.out.println("kB");
//		printArray(obj.knowledgeBaseRaw);
//		
		obj.buildKnowledgeBase(obj.knowledgeBaseRaw);
//		System.out.println("Premesis");
//		obj.printSentences(obj.premises);
//		System.out.println("Consequences");
//		obj.printSentences(obj.consequences);
		
		obj.premise = obj.buildClauses(obj.premises);
		obj.consequence = obj.buildClauses(obj.consequences);
		
//		System.out.println("individual premise with clause number");
//		printClause(obj.premise);
//		
//		System.out.println("individual consequence with clause number");
//		printClause(obj.consequence);
//		
//		
//		String predicate = obj.buildPredicate(obj.query);
//		System.out.println(predicate);
		
		obj.premiseDetails = obj.buildDetails(obj.premise);
		obj.consequenceDetails = obj.buildDetails(obj.consequence);
		
		
		
		obj.queryDetail.premise.arguments = obj.buildArguments(obj.query);
		obj.queryDetail.premise.clauseValue = obj.query;
		obj.queryDetail.premise.predicate = obj.buildPredicate(obj.query);
		obj.queryDetail.premise.sentenceNumber = 99999;
		obj.queryDetail.matched=false;
		
		//obj.matchConsequences(obj.queryDetail);
		obj.buildPremiseMap(obj.premiseDetails);
		obj.queryDetails.add(obj.queryDetail);
		
		//obj.matchConsequences(obj.queryDetail);
		obj.initialMatch = 11111;
		obj.initialMatch = obj.initialMatchWithConsequences(obj.queryDetails.get(0));
		
		obj.backwardChain(obj.queryDetails, null);
		
		
		List<matchedConsequences> initialPremises = obj.premisesToMatch.get(obj.initialMatch);
		if(null!=initialPremises){
			int l=0;
			//check in premisesToMatch
			for(l=0;l<initialPremises.size();l++){
				if(initialPremises.get(l).matched==false){
					break;
				}
			}
			if(l!=initialPremises.size()){
				//System.out.println("query can't be inferred");
				obj.printOutput("FALSE");
			}
			
		}
	}
	
//	public static void printClause(List<clause> arrayList){
//		for(int i=0; i < arrayList.size(); i++){
//			System.out.print(arrayList.get(i).sentenceNumber);
//			System.out.print("      ");
//			System.out.print(arrayList.get(i).clauseValue);
//			
//			System.out.println();
//		}
//	}
	
//	public static void printArray(List<String> arrayList){
//		for(int i=0; i < arrayList.size(); i++){
//			System.out.println(arrayList.get(i));
//		}
//	}

	public void buildKnowledgeBase(List<String> kbRaw){
		String[] words;
		for(int i=0; i< kbRaw.size();i++){
			words = kbRaw.get(i).split("=>");
			if(words.length != 0){
				if(words.length != 1){
					consequences.put(i, words[1]);
				}
				premises.put(i, words[0]);
			}
		}
	}
	
//	public void printSentences(HashMap<Integer, String> dict){
//		for(Integer k:dict.keySet()){
//			System.out.println(dict.get(k));
//		}
//	}

	public List<clause> buildClauses(HashMap<Integer, String> dict){
		String[] words;
		clause pcObj;
		List<clause> clauses = new ArrayList<clause>();
		for(Integer i : dict.keySet()){
			if(dict.get(i)!=null){
				words = dict.get(i).split("&");
				if(words.length != 0){
					for(int j=0; j<words.length;j++){
						pcObj = new clause();
						pcObj.sentenceNumber = i;
						pcObj.clauseValue = words[j];
						clauses.add(pcObj);
					}
				}
			}
		}
		
		return clauses;
	}

	public String buildPredicate(String word){
		int start;
		String temp="";
		if(null !=word){
			start = word.indexOf("(");
			temp = word.substring(0, start);
		}
		
		return temp;
	}
	
	public Boolean checkPremise(details query){
		Boolean argsConstant = false;
		String predicate = buildPredicate(query.clauseValue);
		for(int i=0;i<premiseDetails.size();i++){
			if(premiseDetails.get(i).predicate.equals(predicate)){
				argsConstant = checkArgsForConstant(premiseDetails.get(i).arguments);
				if(argsConstant){
					if(premiseDetails.get(i).clauseValue.equals(query.clauseValue)){
						//System.out.println("Found");
						return true;
					}
				}
				//check if the argument in the premise is assignable and has the same number of arguments
				//premise has a matching constant and the query has a variable at the same position
				if(query.arguments.size()==premiseDetails.get(i).arguments.size()){
					for(int j=0;j<query.arguments.size();j++){
						
						if(query.arguments.size()==1&&isVariable(query.arguments.get(j))&&isConstant(premiseDetails.get(i).arguments.get(j))){
							//String constantValue =  query.arguments.get(j);
							String constantValue = premiseDetails.get(i).arguments.get(j);
							query.arguments.set(j, constantValue);
							return true;
						}
						
						if(j==1){
							if(isConstant(premiseDetails.get(i).arguments.get(j))&&isVariable(query.arguments.get(j))
									&&isConstant(premiseDetails.get(i).arguments.get(j-1))&&isConstant(query.arguments.get(j-1))
									&&premiseDetails.get(i).arguments.get(j-1).equals(query.arguments.get(j-1))){
								String constValue = premiseDetails.get(i).arguments.get(j);
								query.arguments.set(j, constValue);
								return true;
							}
							if(isConstant(premiseDetails.get(i).arguments.get(j-1))&&isVariable(query.arguments.get(j-1))
									&&isConstant(premiseDetails.get(i).arguments.get(j))&&isConstant(query.arguments.get(j))
									&&premiseDetails.get(i).arguments.get(j).equals(query.arguments.get(j))){
								String constValue = premiseDetails.get(i).arguments.get(j-1);
								query.arguments.set(j-1, constValue);
								return true;
							}
						}
					}
				}
				
			}
		}
		return false;
	}
	
	public Boolean checkArgsForConstant(List<String> arguments){
		Boolean allConstant = false;
		int i=0;
		for(i=0;i<arguments.size();i++){
			if(!isConstant(arguments.get(i))){
				break;
			}
		}
		if(i==arguments.size()){
			allConstant=true;
		}		
		
		return allConstant;
	}

	public List<String> buildArguments(String word){
		int start=0, end=0;
		String[] args;
		List<String> arguments = new ArrayList<String>();
		String temp;
		if(null != word){
			start = word.indexOf("(");
			end = word.indexOf(")");
			temp = word.substring(start+1, end);
			args = temp.split(",");
			if(args.length != 0){
				for(int j=0; j<args.length;j++){
					arguments.add(args[j]);
				}
			}
		}
		
		return arguments;
	}

	public details buildClauseDetails(clause clauseObj){
		details detailsObj = new details();
		detailsObj.sentenceNumber = clauseObj.sentenceNumber;
		detailsObj.clauseValue = clauseObj.clauseValue;
		detailsObj.arguments =buildArguments(clauseObj.clauseValue);
		detailsObj.predicate =buildPredicate(clauseObj.clauseValue);
		return detailsObj;
	}
	
	public List<details> buildDetails(List<clause> clauses){
		List<details> details = new ArrayList<details>();
		for(int i=0; i< clauses.size(); i++){
			details.add(buildClauseDetails(clauses.get(i)));
		}
		return details;
	}
	
	public int initialMatchWithConsequences(matchedConsequences queryDetails){
		String queryPredicate = queryDetails.premise.predicate;
		List<String> queryArguments = queryDetails.premise.arguments;
		int matchAtSentence = 99999;
		
		for(int i=0; i<consequenceDetails.size();i++){
			String predicate = consequenceDetails.get(i).predicate;
			int sentenceNumber = consequenceDetails.get(i).sentenceNumber;
			List<String> arguments = consequenceDetails.get(i).arguments;
			Boolean constantsMatch = false;
			Boolean variableAssignable = false;
			String constantValue="";
			if(predicate.equals(queryPredicate)){
				if(queryArguments.size() == arguments.size()){
					for(int j=0; j< arguments.size();j++){
						//check if the argument is constant and is the same as the one in the query
						if(isConstant(arguments.get(j))&&isConstant(queryArguments.get(j))){
							if(arguments.get(j).equals(queryArguments.get(j))){
								constantsMatch = true;
							}
							else{
								break;
							}
						}
						//check if there is a variable in the consequence and a constans in the query
						if(isVariable(arguments.get(j))&&isConstant(queryArguments.get(j))){
							variableAssignable = true;
							constantValue =  queryArguments.get(j);
						}
						
						//check if the query has just one element and is a constant and the corresponding argument in the consequence is a variable.
						if(queryArguments.size()==1&&isVariable(arguments.get(j))&&isConstant(queryArguments.get(j))){
							variableAssignable = true;
							constantsMatch = true;
							constantValue =  queryArguments.get(j);
						}
						//might not be needed
						//check if the query has one element and is a constant and the consequence has the same constant
						if(queryArguments.size()==1&&isConstant(arguments.get(j))&&isConstant(queryArguments.get(j))){
							//check if the constants are the same.
							if(arguments.get(j).equals(queryArguments.get(j))){
								constantsMatch = true;
								variableAssignable = true;
							}
						}
						//might not be needed
						//check if the query has two elements and both are constant and the consequence has the same constants
						if(j==1&&isConstant(arguments.get(j))&&isConstant(queryArguments.get(j))&&isConstant(arguments.get(j-1))&&isConstant(queryArguments.get(j-1))){
							//check if the constants are the same.
							if(arguments.get(j).equals(queryArguments.get(j))&&arguments.get(j).equals(queryArguments.get(j))){
								constantsMatch = true;
								variableAssignable = true;
							}
						}
						
					}
				}
				if(constantsMatch && variableAssignable){
					matchAtSentence = sentenceNumber;
					return matchAtSentence;
				}
			}
		}
		return matchAtSentence;
	}

	public int matchConsequences(matchedConsequences queryDetails){
		List<matchedConsequences> matchedDetails;
		String queryPredicate = queryDetails.premise.predicate;
		List<String> queryArguments = queryDetails.premise.arguments;
		int matchAtSentence = 99999;
		
		for(int i=0; i<consequenceDetails.size();i++){
			String predicate = consequenceDetails.get(i).predicate;
			int sentenceNumber = consequenceDetails.get(i).sentenceNumber;
			List<String> arguments = consequenceDetails.get(i).arguments;
			Boolean constantsMatch = false;
			Boolean variableAssignable = false;
			String constantValue="";
			if(predicate.equals(queryPredicate)){
				if(queryArguments.size() == arguments.size()){
					for(int j=0; j< arguments.size();j++){
						//check if the argument is constant and is the same as the one in the query
						if(isConstant(arguments.get(j))&&isConstant(queryArguments.get(j))){
							if(arguments.get(j).equals(queryArguments.get(j))){
								constantsMatch = true;
							}
							else{
								break;
							}
						}
						//check if there is a variable in the consequence and a constants in the query
						if(isVariable(arguments.get(j))&&isConstant(queryArguments.get(j))){
							variableAssignable = true;
							constantValue =  queryArguments.get(j);
						}
						
						//check if the query has just one element and is a constant and the corresponding argument in the consequence is a variable.
						if(queryArguments.size()==1&&isVariable(arguments.get(j))&&isConstant(queryArguments.get(j))){
							variableAssignable = true;
							constantsMatch = true;
							constantValue =  queryArguments.get(j);
						}
						//might not be needed
						//check if the query has one element and is a constant and the consequence has the same constant
						if(queryArguments.size()==1&&isConstant(arguments.get(j))&&isConstant(queryArguments.get(j))){
							//check if the constants are the same.
							if(arguments.get(j).equals(queryArguments.get(j))){
								constantsMatch = true;
								variableAssignable = true;
							}
						}
						//might not be needed
						//check if the query has two elements and both are constant and the consequence has the same constants
						if(j==1&&isConstant(arguments.get(j))&&isConstant(queryArguments.get(j))&&isConstant(arguments.get(j-1))&&isConstant(queryArguments.get(j-1))){
							//check if the constants are the same.
							if(arguments.get(j).equals(queryArguments.get(j))&&arguments.get(j-1).equals(queryArguments.get(j-1))){
								constantsMatch = true;
								variableAssignable = true;
							}
						}
						//might not be needed
						//check if the query has just one argument and is a variable
						if(queryArguments.size()==1&&isVariable(arguments.get(j))&&isVariable(queryArguments.get(j))){
							variableAssignable=true;
							constantsMatch = true;
						}
						
						//might not be needed
						//if the query has 2 arguments and one of them is a variable and the constant matches
						//with the constant value in the kb either at pos 0 or 1. and the corresponding clause in 
						//the kb also has a variable at the same position
						if(j==1){
							if(isVariable(arguments.get(j))&&isVariable(queryArguments.get(j))
									&&isConstant(arguments.get(j-1))&&isConstant(queryArguments.get(j-1))
									&&arguments.get(j-1).equals(queryArguments.get(j-1))
									||isVariable(arguments.get(j-1))&&isVariable(queryArguments.get(j-1))
									&&isConstant(arguments.get(j))&&isConstant(queryArguments.get(j))
									&&arguments.get(j).equals(queryArguments.get(j))){
								variableAssignable=true;
								constantsMatch = true;
							}
						}
						//might not be needed
						//if the query has 2 arguments and one of them is a variable and the constant matches
						//with the constant value in the kb either at pos 0 or 1. and the corresponding clause in 
						//the kb also has a constant at the same position
						if(j==1){
							if(isConstant(arguments.get(j))&&isVariable(queryArguments.get(j))
									&&isConstant(arguments.get(j-1))&&isConstant(queryArguments.get(j-1))
									&&arguments.get(j-1).equals(queryArguments.get(j-1))
									||isConstant(arguments.get(j-1))&&isVariable(queryArguments.get(j-1))
									&&isConstant(arguments.get(j))&&isConstant(queryArguments.get(j))
									&&arguments.get(j).equals(queryArguments.get(j))){
								variableAssignable=true;
								constantsMatch = true;
							}
						}
					}
				}
				if(constantsMatch && variableAssignable){
					List<details> detailsObj = new ArrayList<details>();
					for(details detail: premiseMap.get(consequenceDetails.get(i).sentenceNumber)){
						details tempObj = new details();
						tempObj.clauseValue = detail.clauseValue;
						tempObj.predicate = detail.predicate;
						tempObj.sentenceNumber = detail.sentenceNumber;
						for(String arg: detail.arguments){
							tempObj.arguments.add(arg);
						}
						detailsObj.add(tempObj);
					}
					
					//replace the variable with the constant value
					for(int k=0;k<detailsObj.size();k++){
						//if there was no constant matching value then don't replace the argument value
						if(!constantValue.equals("")){
							List<String> args = new ArrayList<String>();
							for(String arg : detailsObj.get(k).arguments){
								args.add(arg); 
							}
							for(int l=0;l<args.size();l++){
								if(isVariable(args.get(l))){
									args.set(l, constantValue);
								}
							}
							detailsObj.get(k).arguments=args;
						}
						detailsObj.get(k).clauseValue = buildWithConstant(detailsObj.get(k));
						matchedConsequences mcObj = new matchedConsequences();
						
						mcObj.matched = false;
						mcObj.premise = detailsObj.get(k);
						matchedDetails = premisesToMatch.get(sentenceNumber);
						if(matchedDetails != null){
							matchedDetails.add(mcObj);
							premisesToMatch.put(sentenceNumber, matchedDetails);
						}
						else{
							List<matchedConsequences> temp=new ArrayList<matchedConsequences>();
							temp.add(mcObj);
							premisesToMatch.put(sentenceNumber, temp);
						}
					}
					matchAtSentence = sentenceNumber;
					matchedConsequences mc = new matchedConsequences();
					consequencesToMatch.put(sentenceNumber, queryDetails);
					return matchAtSentence;
				}
			}
		}
		return matchAtSentence;
	}
	
	public Boolean isVariable(String var){
		return (Character.isLowerCase(var.charAt(0)));
	}
	
	public Boolean isConstant(String var){
		return (Character.isUpperCase(var.charAt(0)));
	}
	
	public void buildPremiseMap(List<details> premiseDetails){
		List<details> premiseDetail;
		Integer sentenceNumber;
		for(int i=0; i<premiseDetails.size();i++){
			sentenceNumber = premiseDetails.get(i).sentenceNumber;
			premiseDetail = premiseMap.get(sentenceNumber);
			if(null != premiseDetail){
				premiseDetail.add(premiseDetails.get(i));
				premiseMap.put(sentenceNumber, premiseDetail);
			}
			else{
				List<details> temp = new ArrayList<details>();
				temp.add(premiseDetails.get(i));
				premiseMap.put(sentenceNumber, temp);
			}
		}
	}

	public String buildWithConstant(details clauseDetails){
		String clauseVal = clauseDetails.predicate+"(";
		for(int i=0;i<clauseDetails.arguments.size();i++){
			clauseVal+=clauseDetails.arguments.get(i);
			if(i!=clauseDetails.arguments.size()-1)
				clauseVal+=",";
		}
		clauseVal+=")";
		return clauseVal;
	}

	//recursively set the consequence to true if all the premises are true
	public void setPremiseTrue(matchedConsequences clause){
		matchedConsequences consequence = consequencesToMatch.get(clause.premise.sentenceNumber);
		consequence.matched=true;
		int prevSentenceNo = 99999;
		for(Object value: premisesToMatch.values()){
			if(value instanceof List<?>){
				List<matchedConsequences> temp = (List<matchedConsequences>)(value);
				for(matchedConsequences mc:temp){
					if(mc.premise.clauseValue.equals(consequence.premise.clauseValue)){
						prevSentenceNo = mc.premise.sentenceNumber;
						break;
					}
				}
			}
		}
		List<matchedConsequences> premises = premisesToMatch.get(prevSentenceNo);
		if(premises!=null){
			for(int j=0;j<premises.size();j++){
				if(premises.get(j).premise.predicate.equals(clause.premise.predicate)){
					premises.get(j).matched=true;
				}
			}
			int j=0;
			//check in premisesToMatch
			for(j=0;j<premises.size();j++){
				if(premises.get(j).matched==false){
					break;
				}
			}
			if(j==premises.size()){
				setPremiseTrue(premises.get(0));
			}
		}
	}
	public Boolean backwardChain(List<matchedConsequences> queryDetails, matchedConsequences prevCons){
		
		for(int i=0;i<queryDetails.size();i++){
			Boolean foundInPremise = checkPremise(queryDetails.get(i).premise);
			if(foundInPremise){
				//check if all other premises of the same sentence have been satisfied too.
				List<matchedConsequences> premises = premisesToMatch.get(queryDetails.get(i).premise.sentenceNumber);
				if(premises==null){
					//this is the case where the query is found directly in the KB w/o
					//requiring BC.
//					System.out.println("found the result of query in KB directly");
//					System.out.println("query inferrred");
					printOutput("TRUE");
					//return true;
					return true;
				}
				else{
					//set the premise to matched
					for(int j=0;j<premises.size();j++){
						if(premises.get(j).premise.predicate.equals(queryDetails.get(i).premise.predicate)){
							premises.get(j).matched=true;
						}
					}
					//check if all premises are matched.
					int j=0;
					//check in premisesToMatch
					for(j=0;j<premises.size();j++){
						if(premises.get(j).matched==false){
							break;
						}
					}
					if(j==premises.size()){
						//all premise predicates matched
						//System.out.println("found all premisis at this level");
						//the consequence is true.
						//set the corresponding premise to true.
						//this must be done recursively
//						List<matchedConsequences> prevConsequence = premisesToMatch.get(prevCons.premise.sentenceNumber);
//						if(prevConsequence!=null){
//							for(matchedConsequences obj : prevConsequence){
//								if(obj.premise.clauseValue.equals(prevCons.premise.clauseValue))
//									obj.matched=true;
//							}
//						}
						setPremiseTrue(premises.get(0));
						
						List<matchedConsequences> initialPremises = premisesToMatch.get(initialMatch);
						if(null==initialPremises){
							//the query never matched any of the consequences
							//nothing can be inferred
							//System.out.println("query can't be inferred");
							printOutput("FALSE");
						}
						else{
							int l=0;
							//check in premisesToMatch
							for(l=0;l<initialPremises.size();l++){
								if(initialPremises.get(l).matched==false){
									break;
								}
							}
							if(l==initialPremises.size()){
								//System.out.println("query inferred");
								printOutput("TRUE");
								return true;
							}
						}
					}
				}
			}
			else{
				
				if(initialMatch==99999){
					printOutput("FALSE");
					return false;
				}
				else{
					int matchAt = matchConsequences(queryDetails.get(i));
					//call backward chain on premises of the same sentence as query details which haven't been matched
					List<matchedConsequences> premises = new ArrayList<matchedConsequences>();
					List<matchedConsequences> premisesToRun = new ArrayList<matchedConsequences>();
					premises = premisesToMatch.get(matchAt);
					if(premises!=null){
						for(matchedConsequences mc : premises){
							if(mc.matched==false){
								premisesToRun.add(mc);
							}
						}
						backwardChain(premisesToRun, queryDetails.get(i));
					}
					
				}
			}
		}
		return false;
	}
	
	public void printOutput(String text){
		try{
			File file = new File("output.txt");
			if(!file.exists()){
				file.createNewFile();
			}
			FileWriter fileWriter = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bufferedWriter = new BufferedWriter(fileWriter);
			
			bufferedWriter.write(text);
			bufferedWriter.close();
		}catch(IOException e){
			System.out.println("this is embarrasing");
		}
	}

}

class clause{
	int sentenceNumber;
	String clauseValue;
}

class details{
	int sentenceNumber;
	String predicate;
	String clauseValue;
	List<String> arguments = new ArrayList<String>();
}

class matchedConsequences{
	Boolean matched;
	details premise = new details();
}



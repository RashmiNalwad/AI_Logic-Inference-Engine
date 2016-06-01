import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

class Arg{ // Class to differentiate variables and constants in clauses.
	String var;
	String value;
	boolean isVar = false; // Assuming all are constants
	public Arg(String var,boolean isVar,String value)
	{
		this.var = var;
		this.isVar = isVar;
		this.value = value;
	}
	public Arg()
	{

	}
}

class Structure
{
	String pred;
	ArrayList<String> var;
	boolean isNegate = false;
	ArrayList<Arg> arg;
	boolean eval = false;
	HashMap<String, ArrayList<String>> childMap = new HashMap<String, ArrayList<String>>(); // Populated only if premise which has conjunction and whose value is evaluated to true

	public Structure(String pred,ArrayList<String> var,boolean isNegate,ArrayList<Arg> args,boolean eval,HashMap<String, ArrayList<String>> childMap)
	{
		this.pred = pred;
		this.var = var;
		this.isNegate = isNegate;
		this.arg = args;
		this.eval = eval;
		this.childMap = childMap;	
	}

	public Structure()
	{

	}
}

public class inference {

	private static HashMap<String, Structure> tokenQueryMap; // Tokenized Query Map
	private static HashMap<String, Structure> tokenClauseMap;

	private static final String FALSE = "FALSE" + "\n";
	private static final String TRUE = "TRUE" + "\n";

	private static LinkedHashMap<String, Boolean> read_input_file(String[] args) 
	{
		File inFile = null;
		if (0 < args.length) {
			inFile = new File(args[1]);
		}
		BufferedReader br = null;
		try
		{
			br = new BufferedReader(new FileReader(inFile));
			String query = "";
			String clause = "";
			int numOfQueries = Integer.parseInt(br.readLine());
			LinkedHashMap<String,Boolean> queryMap = new LinkedHashMap<String, Boolean>();
			for (int i = 0 ;i < numOfQueries;i++)
			{
				query = br.readLine();
				queryMap.put(query, false);
			}
			int numOfClauses = Integer.parseInt(br.readLine());
			HashMap<String, ArrayList<String>> clauseMap = new HashMap<String, ArrayList<String>>(); // Map of Clauses separated by => with conclusion as key and premise as value.
			ArrayList<String> clauseList = new ArrayList<String>();    // List of known facts in KB	   
			for(int j = 0; j < numOfClauses;j++)
			{
				clause = br.readLine();
				if(clause.contains("=>"))
				{
					String[] clau = clause.split(" => ");
					if ( clauseMap.get(clau[1])== null)
					{
						clauseMap.put(clau[1], new ArrayList<String>());
						clauseMap.get(clau[1]).add(clau[0]);    			  
					}
					else
					{
						clauseMap.get(clau[1]).add(clau[0]);
					}
				}
				else
				{
					clauseList.add(clause);
				}

			}
			tokenQueryMap = tokenize_query(queryMap,null); 
			do_backward_chaining(queryMap,tokenQueryMap,clauseList,clauseMap);
			return queryMap;
		}
		catch(IOException e)
		{
			e.printStackTrace();
		}
		finally
		{
			try
			{
				if (br != null)br.close();
			}
			catch (IOException ex) 
			{
				ex.printStackTrace();
			}
		}
		return null;
	}

	private static void do_backward_chaining(LinkedHashMap<String, Boolean> queryMap,HashMap<String, Structure> tokenQueryMap,ArrayList<String> clauseList,HashMap<String, ArrayList<String>> clauseMap)
	{
		for(String query:queryMap.keySet())
		{
			try
			{
				tokenClauseMap = tokenize(clauseMap);// Only Keys of clause map are tokenised.
				Structure qs = tokenQueryMap.get(query);
				for(String clause: clauseMap.keySet())
				{
					if(clause.startsWith(qs.pred)|| clause.startsWith("~" + qs.pred)) //Doubt
					{
						boolean value = evaluate_premise(clauseMap,clause,clauseList,queryMap,query,tokenClauseMap,true,true,clause,query);
						Structure qu = tokenQueryMap.get(query); // For checking if query starts with negation.
						Structure qc = tokenClauseMap.get(clause);
						if((qu.isNegate != true && qc.isNegate == true) || (qu.isNegate == true && qc.isNegate != true)) // Need to Test Negating of clauses part
						{
							value = !value;
						}
						if(value == true)
						{
							queryMap.replace(query, false, value); // Writing evaluated boolean value of query to map. 
						}
					}
				}
			}
			catch(Exception e)
			{
				e.printStackTrace();
				continue;
			}
		}
	}

	private static boolean evaluate_premise(HashMap<String, ArrayList<String>> clauseMap, String clause,ArrayList<String> clauseList, LinkedHashMap<String, Boolean> queryMap, String query,HashMap<String, Structure> tokenClauseMap,boolean fromBackwardChaining, boolean level1, String startClause, String startQuery) 
	{
		ArrayList<String> premises = clauseMap.get(clause);
		Structure qs=tokenQueryMap.get(query);
		ArrayList<String> subs = qs.var;

		Structure cs = tokenClauseMap.get(clause);
		ArrayList<Arg> carg = cs.arg;
		
		if(!query.equals(startQuery))
		{
			tokenClauseMap = tokenize(clauseMap);
		}

		if(level1)
		{
			for(int j =0;j<subs.size();j++)
			{
				carg.get(j).value = subs.get(j);
			}	
		}

		boolean value = false;
		for(int i=0;i<premises.size();i++) // Iterating between possible premises for same key.
		{
			value = compute_value(premises.get(i),clause,carg,clauseMap,tokenClauseMap,clauseList,queryMap,query,startClause,startQuery); 
			if(value == true)
			{
				return value;
			}
		}
		return value; 
	}

	private static boolean compute_value(String premises,String parent,ArrayList<Arg> carg, HashMap<String, ArrayList<String>> clauseMap, HashMap<String, Structure> tokenClauseMap, ArrayList<String> clauseList,LinkedHashMap<String, Boolean> queryMap, String query, String startClause,String startQuery) 
	{
		// Recursive function
		boolean premise_value = true;
		if(premises.contains("^"))
		{
			boolean queryUpdated = false;
			String[] conjPrem = premises.split(" \\^ ");
			HashMap<String, Boolean> map = new HashMap<String, Boolean>(); // Map of premises between ^ and its value set to false
			for(int q=0; q<conjPrem.length ; q++) // remove and break loop when 1 clause evaluates to false 
			{
				map.put(conjPrem[q], false);
			}
			for(String key: map.keySet())
			{
				if(clauseList.contains(key))
				{
					map.put(key, true);
					continue;
				}
				String formed_value = "";
				if(queryUpdated && key.startsWith(tokenize(startQuery).pred))
				{
					query= key;
				}
				HashMap<String, ArrayList<String>> subsMap = new HashMap<String, ArrayList<String>>();// Map of possible subs values.
				HashMap<String, ArrayList<String>> matchedMap = new HashMap<String, ArrayList<String>>();// Map of possible matched var values which to be put in parents map.
				Structure qs = tokenize(key);
				ArrayList<Arg> arguments = qs.arg; //Keys arguments.
				String args = "";
				Structure queryToken = tokenize(query);

				for(int j =0;j<carg.size();j++)
				{
					for(int a =0;a<arguments.size();a++)
					{
						if(arguments.get(a).var.equals(carg.get(j).var)) // Unification
						{
							if((arguments.get(a).value == null))
								arguments.get(a).value = carg.get(j).value;
						}
						else if(arguments.get(a).var.matches("[A-Z]+[a-z]*"))
						{
							arguments.get(a).value =  arguments.get(a).var;
						}
							
					}

				}	
				for(int k=0;k<arguments.size();k++)
				{
					if(args.isEmpty())
					{
						args = args + arguments.get(k).value;
					}
					else
					{
						args = args + "," + arguments.get(k).value;
					}
				}
				if(premises.contains("("))
				{
					formed_value = qs.pred + "(" + args + ")";
				}
				else
				{
					formed_value = qs.pred;
				}
				if(clauseList.contains(formed_value)) // If there is a case like B(John,null) need to substitute different values and see if it satisfies.
				{
					map.replace(key, false, true);
					premise_value = true;
					continue;
				}
				else if (query.equals(formed_value) || query.equals("~"+formed_value)) // Needs testing for all looping cases. 
				{
					if(tokenClauseMap.get(premises)!= null)
						tokenClauseMap.get(premises).eval = false;
					return false;
				}
				else if ( key.startsWith(queryToken.pred)|| key.startsWith("~" + queryToken.pred))
				{
					query = key;
					queryUpdated = true;
					HashMap<String, Structure> queryTok = tokenize_query(null,query);
					tokenQueryMap.put(query, queryTok.get(query));
					boolean val = evaluate_premise(clauseMap, startClause, clauseList, queryMap, query, tokenClauseMap, false, true, startClause,startQuery);
					map.put(key, val);	
				}
				else // Need to put diff values and check if it exists in KB
				{
					if(tokenClauseMap.get(parent).childMap.isEmpty()) // If Parents is not having any var to substitute, match facts from KB
					{
						matchFacts(clauseList,arguments,subsMap,parent,map,carg,key,matchedMap,qs);
					}
					else // Take values from parent and substitute the values
					{
						HashMap<String, ArrayList<String>> inheritedValues = tokenClauseMap.get(parent).childMap;
						boolean clausePresent = false;
						ArrayList<String> clause = new ArrayList<String>();
						for(String cla: clauseMap.keySet())
						{
							if(cla.startsWith(qs.pred))
							{
								if(tokenClauseMap.get(cla).pred.equals(qs.pred))
								{
									clausePresent = true;
									clause.add(cla);
								}
							}
						}
						for(String iVar : inheritedValues.keySet())
						{
							for(String iValue:inheritedValues.get(iVar))
							{
								Collection<Arg> dummy_arg = new ArrayList<Arg>();
								for(Arg argu :arguments)
								{
									dummy_arg.add(new Arg(argu.var,argu.isVar,argu.value)); // Deep copying values from Argum to dummy
								}   
								for(Arg dumArg : dummy_arg)
								{
									if(dumArg.var.equals(iVar))
									{
										if(dumArg.value == null)
										{
											dumArg.value = iValue;
										}
									}
								}
								String matchedArgs = "";
								for(int k=0;k<dummy_arg.size();k++)
								{
									if(matchedArgs.isEmpty())
									{
										matchedArgs = matchedArgs + ((ArrayList<Arg>) dummy_arg).get(k).value;
									}
									else
									{
										matchedArgs = matchedArgs + "," + ((ArrayList<Arg>) dummy_arg).get(k).value;
									}
								}
								String matched_value = qs.pred + "(" + matchedArgs + ")";
								if(clauseList.contains(matched_value))
								{
									map.put(key, true);
									for(Arg dumArg: dummy_arg)
									{
										if(dumArg.var.equals(iVar))
										{
											if(matchedMap.isEmpty())
											{
												matchedMap.put(iVar, new ArrayList<String>());
												matchedMap.get(iVar).add(dumArg.value);
											}
											else
											{
												matchedMap.get(iVar).add(dumArg.value);
											}		
										}
									}
								}
							}
						}
						if(clausePresent && map.get(key) == false) //Arguments matching and updating childmap and passing to child.
						{   
							for(int e=0;e<clause.size();e++)
							{
								HashMap<String, ArrayList<String>> inheritMap = new HashMap<String, ArrayList<String>>();
								Structure claStruc = tokenClauseMap.get(clause.get(e));
								ArrayList<Arg> claArg = claStruc.arg;
								int size = Integer.max(arguments.size(),claArg.size());
								for(int t=0;t<size;t++)
								{
									if(arguments.get(t) != null && claArg.get(t) != null)
									{
										if(!arguments.get(t).var.equals(claArg.get(t).var))
										{
											if(tokenClauseMap.get(parent).childMap.containsKey(arguments.get(t).var))
											{
												inheritMap.put(claArg.get(t).var, tokenClauseMap.get(parent).childMap.get(arguments.get(t).var));
											}
										}
									}
								}								
								if(!inheritMap.isEmpty())
								{
									tokenClauseMap.get(clause.get(e)).childMap = inheritMap;
								}
								else
								{
									tokenClauseMap.get(clause.get(e)).childMap = copy(tokenClauseMap.get(parent).childMap);
								}
							}
						}
		
					}
				}
				ArrayList<String> matchedFacts = new ArrayList<String>(); // List holding possible facts that can be matched.
				for(int l=0;l<clauseList.size();l++)
				{
					if(clauseList.get(l).startsWith(qs.pred)||clauseList.get(l).startsWith("~" + qs.pred))
					{
						matchedFacts.add(clauseList.get(l));
					}
				}
				boolean clausePresent = false;
				ArrayList<String> clause = new ArrayList<String>();
				for(String cla: clauseMap.keySet())
				{
					if(cla.startsWith(qs.pred))
					{
						if(tokenClauseMap.get(cla).pred.equals(qs.pred))
						{
							clausePresent = true;
							clause.add(cla);
						}
					}
				}
				if(clauseMap.keySet().contains(key) && map.get(key) == false) // Checking if it has premises if so its premises should be evaluated.
				{
					tokenClauseMap.replace(key, qs);
					tokenClauseMap.get(key).childMap = copy(tokenClauseMap.get(parent).childMap); //Passing other branches values to next branch from parent
					premise_value = evaluate_premise(clauseMap, key, clauseList, queryMap, query, tokenClauseMap,false,false,startClause,startQuery);
				    map.put(key, premise_value);
				}	
				else if(clausePresent && map.get(key) == false)
				{
					for(int o = 0;o<clause.size();o++)
					{
						for(int j=0;j<clauseMap.get(clause.get(o)).size();j++) // Evaluating Premises of Premise in loop. (2nd level)
						{
							Structure cs = tokenClauseMap.get(clause.get(o));
							ArrayList<Arg> cargs = cs.arg;
							for(int s=0;s<cargs.size();s++) // Taking previous values.
							{
								cargs.get(s).value = arguments.get(s).value;
							}	
							premise_value = compute_value(clauseMap.get(clause.get(o)).get(j),clause.get(o),cargs,clauseMap,tokenClauseMap,clauseList,queryMap,query,startClause,startQuery);
							if ( premise_value == true)
							{
								map.replace(key, false, true);
								//Updating Parent( Self )Map like Hostile(x) => Hostile(z) 
								HashMap<String, ArrayList<String>> childMap = tokenClauseMap.get(clause.get(o)).childMap;
								Structure childStru = tokenClauseMap.get(clause.get(o));
								ArrayList<Arg> childArg = childStru.arg;
								HashMap<String, ArrayList<String>> parentMap = new HashMap<String, ArrayList<String>>();
								for(int t=0;t<arguments.size();t++)
								{
									if(arguments.get(t).value == null )
									{
										for(String var :childMap.keySet())
										{
											if(childArg.get(t).var.equals(var))
											{
												parentMap.put(arguments.get(t).var, childMap.get(var));
											}
										}
									}
								}								
								tokenClauseMap.get(parent).childMap.putAll(parentMap);
								break;
							}
						}
					}
				}
				else //One of the clauses in the ^ string is false. Break the loop
				{
					if(matchedMap.isEmpty() && !matchedFacts.isEmpty())
					{
						boolean nullPresent = false;
						boolean inheritValueMatched = false; // First checking if from inherited values from parent we are getting the fact.
						HashMap<String, ArrayList<String>> inheritVal = new HashMap<String, ArrayList<String>>();
						ArrayList<HashMap<String, String>> resultMap = new ArrayList<HashMap<String, String>>();
						if(!tokenClauseMap.get(parent).childMap.isEmpty())
						{
							for(int k = 0; k< arguments.size();k++)
							{
								if(arguments.get(k).value == null)
								{
									if(tokenClauseMap.get(parent).childMap.containsKey(arguments.get(k).var))
									{
										inheritVal.put(arguments.get(k).var, tokenClauseMap.get(parent).childMap.get(arguments.get(k).var));
									}
								}
							}

							if(!inheritVal.isEmpty())
							{
								ArrayList<ArrayList<String>> list = new ArrayList<ArrayList<String>>(inheritVal.values());
								ArrayList<String> keyList = new ArrayList<String>(inheritVal.keySet());
								GeneratePermutations(list, 0, "", resultMap, keyList);
							}
						}
						
						for(HashMap<String, String> rmap:resultMap)
						{
							String margs = "";
							String formedVal = "";
							for(int k=0;k<arguments.size();k++)
							{
								if(margs.isEmpty())
								{
									if(arguments.get(k).value == null)
									{
										arguments.get(k).value = rmap.get(arguments.get(k).var);
									}
									else
									{
										arguments.get(k).value = arguments.get(k).value;
									}
									margs = margs + arguments.get(k).value;
								}
								else
								{
									if(arguments.get(k).value == null)
									{
										arguments.get(k).value = rmap.get(arguments.get(k).var);
									}
									else
									{
										arguments.get(k).value = arguments.get(k).value;
									}
									margs = margs + "," + arguments.get(k).value;
								}
							}
							if(premises.contains("("))
							{
								formedVal = qs.pred + "(" + margs + ")";
							}
							else
							{
								formedVal = qs.pred;
							}
							if(clauseList.contains(formedVal))
							{
								inheritValueMatched = true;
								break;
							}
							else if(formedVal.contains("null"))
							{
								nullPresent = true;
							}
						}
						if( inheritValueMatched )
						{
						   premise_value = true;
						}
						else if( !inheritVal.isEmpty() && inheritValueMatched == false && nullPresent == false)
						{
							premise_value = false;
						}
						else
						{
							HashMap<String, ArrayList<String>> subMap = new HashMap<String, ArrayList<String>>();// Map of possible subs values.
							HashMap<String, Boolean> maps = new HashMap<String, Boolean>(); // Map of premises between ^ and its value set to false
							HashMap<String, ArrayList<String>> matchedMaps = new HashMap<String, ArrayList<String>>();// Map of possible matched var values which to be put in parents map.
							maps.put(key, false);
							ArrayList<Arg> cargs = qs.arg;
							matchFacts(clauseList,arguments,subMap,parent,maps,cargs,key,matchedMaps,qs);
							if(maps.get(key) == false)
							{
								return false;
							}
							else
							{
								map.replace(key, false, true);
								// Updating parents map with true subs only if its evaluate to true
								ArrayList<Arg> parentArg = tokenClauseMap.get(parent).arg;

								HashMap<String, ArrayList<String>> parentMap = new HashMap<String, ArrayList<String>>();
								for(int t=0;t<arguments.size();t++)
								{
									if(arguments.get(t).value == null )
									{
										if(matchedMaps.containsKey(arguments.get(t).var))
										{
											for(Arg parVar : parentArg)
											{
												if(parVar.var.equals(arguments.get(t).var))
												{
													parentMap.put(parVar.var, matchedMaps.get(arguments.get(t).var));
												}
												else
												{
													parentMap.put(arguments.get(t).var, matchedMaps.get(arguments.get(t).var));
												}
											}
										}
									}
								}								
								tokenClauseMap.get(parent).childMap.putAll(parentMap);
							} 
						}
					}
					else if(map.get(key) == false)
					{
						premise_value = false;
						break;
					}
					else
					{
                       // Updating parents map with true subs only if its evaluate to true
						ArrayList<Arg> parentArg = tokenClauseMap.get(parent).arg;
					    
					    HashMap<String, ArrayList<String>> parentMap = new HashMap<String, ArrayList<String>>();
						for(int t=0;t<arguments.size();t++)
						{
							if(arguments.get(t).value == null )
							{
								if(matchedMap.containsKey(arguments.get(t).var))
								{
									for(Arg parVar : parentArg)
									{
										if(parVar.var.equals(arguments.get(t).var))
										{
											parentMap.put(parVar.var, matchedMap.get(arguments.get(t).var));
										}
										else
										{
											parentMap.put(arguments.get(t).var, matchedMap.get(arguments.get(t).var));
										}
									}
								}
						    }
							else
							{
								parentMap.put(arguments.get(t).var, new ArrayList<String>());
								parentMap.get(arguments.get(t).var).add(arguments.get(t).value);
							}
						}								
						tokenClauseMap.get(parent).childMap.putAll(parentMap);
					}
				}
				if(premise_value == false)
				{
					break;
				}
			}
		}
		else
		{
			HashMap<String, Boolean> map = new HashMap<String, Boolean>(); // Map of premises between ^ and its value set to false
			map.put(premises, false);
			if(clauseList.contains(premises))
			{
				map.put(premises, true);
				return true;
			}
			boolean clausePresent = false;
			ArrayList<String> clause = new ArrayList<String>();
			for(String key: clauseMap.keySet())
			{
				if(key.startsWith(tokenize(premises).pred))
				{
					if(tokenClauseMap.get(key).pred.equals(tokenize(premises).pred))
					{
						clausePresent = true;
						clause.add(key);
					}
				}
			}
			ArrayList<Arg> arguments= null;
			Structure tok_clause = tokenClauseMap.get(premises);
			Structure non_clause = null;
			String formed_value = "";
			Structure qs = null;
			Structure queryToken = tokenize(query);
			if ( tok_clause == null)
			{
				non_clause = tokenize(premises);
				qs = non_clause;
				arguments = non_clause.arg;
			}
			else
			{
				qs = tok_clause;
				arguments = tok_clause.arg;
			}
			String args = "";
			for(int j =0;j<carg.size();j++)
			{
				for(int a =0;a<arguments.size();a++)
				{
					if(arguments.get(a).var.equals(carg.get(j).var))
					{
						if((arguments.get(a).value == null))
							arguments.get(a).value = carg.get(j).value;
					}
					else if(arguments.get(a).var.matches("[A-Z]+[a-z]*"))
					{
						arguments.get(a).value = arguments.get(a).var; 
					}
				}
			}	
			for(int k=0;k<arguments.size();k++)
			{
				if(args.isEmpty())
				{
					args = args + arguments.get(k).value;
				}
				else
				{
					args = args + "," + arguments.get(k).value;
				}
			}
			if ( tok_clause == null)
			{
				if(premises.contains("("))
				{
					formed_value = non_clause.pred + "(" + args + ")";
				}
				else
				{
					formed_value = non_clause.pred;
				}
			}
			else
			{
				if(premises.contains("("))
				{
					formed_value = tok_clause.pred + "(" + args + ")";
				}
				else
				{
					formed_value = tok_clause.pred;
				}
			}
			ArrayList<String> matchedFacts = new ArrayList<String>(); // List holding possible facts that can be matched.
			for(int l=0;l<clauseList.size();l++)
			{
				if(clauseList.get(l).startsWith(qs.pred)||clauseList.get(l).startsWith("~" + qs.pred))
				{
					matchedFacts.add(clauseList.get(l));
				}
			}
			if(clauseList.contains(formed_value)) // If Present as a fact in KB
			{
				if(tokenClauseMap.get(premises)!= null)
					tokenClauseMap.get(premises).eval = true;
				return true;
			}
			else if (query.equals(formed_value) || query.equals("~"+formed_value)) // Needs testing for all looping cases. 
			{
				if(tokenClauseMap.get(premises)!= null)
					tokenClauseMap.get(premises).eval = false;
				return false;
			}
			else if ( premises.startsWith(queryToken.pred)|| premises.startsWith("~" + queryToken.pred))
			{
				query = premises;
				HashMap<String, Structure> queryTok = tokenize_query(null,query);
				tokenQueryMap.put(query, queryTok.get(query));
				evaluate_premise(clauseMap, startClause, clauseList, queryMap, query, tokenClauseMap, false, true, startClause,startQuery);
			}
			if(!matchedFacts.isEmpty())// If by substituting different values to the arguments check if it can be proved by KB.
			{
				boolean nullPresent = false;
				boolean inheritValueMatched = false; // First checking if from inherited values from parent we are getting the fact.
				HashMap<String, ArrayList<String>> inheritVal = new HashMap<String, ArrayList<String>>();
				ArrayList<HashMap<String, String>> resultMap = new ArrayList<HashMap<String, String>>();
				if(!tokenClauseMap.get(parent).childMap.isEmpty())
				{
					for(int k = 0; k< arguments.size();k++)
					{
						if(arguments.get(k).value == null)
						{
							if(tokenClauseMap.get(parent).childMap.containsKey(arguments.get(k).var))
							{
								inheritVal.put(arguments.get(k).var, tokenClauseMap.get(parent).childMap.get(arguments.get(k).var));
							}
						}
					}

					if(!inheritVal.isEmpty())
					{
						ArrayList<ArrayList<String>> list = new ArrayList<ArrayList<String>>(inheritVal.values());
						ArrayList<String> keyList = new ArrayList<String>(inheritVal.keySet());
						GeneratePermutations(list, 0, "", resultMap, keyList);
					}
				}
				
				for(HashMap<String, String> rmap:resultMap)
				{
					String margs = "";
					String formedVal = "";
					for(int k=0;k<arguments.size();k++)
					{
						if(margs.isEmpty())
						{
							if(arguments.get(k).value == null)
							{
								arguments.get(k).value = rmap.get(arguments.get(k).var);
							}
							else
							{
								arguments.get(k).value = arguments.get(k).value;
							}
							margs = margs + arguments.get(k).value;
						}
						else
						{
							if(arguments.get(k).value == null)
							{
								arguments.get(k).value = rmap.get(arguments.get(k).var);
							}
							else
							{
								arguments.get(k).value = arguments.get(k).value;
							}
							margs = margs + "," + arguments.get(k).value;
						}
					}
					if ( tok_clause == null)
					{
						if(premises.contains("("))
						{
							formedVal = non_clause.pred + "(" + margs + ")";
						}
						else
						{
							formedVal = non_clause.pred;
						}
					}
					else
					{
						if(premises.contains("("))
						{
							formedVal = tok_clause.pred + "(" + margs + ")";
						}
						else
						{
							formedVal = tok_clause.pred;
						}
					}
					if(clauseList.contains(formedVal))
					{
						inheritValueMatched = true;
						map.put(premises, true);
						break;
					}
					else if(formedVal.contains("null"))
					{
						nullPresent = true;
					}
				}
				
				if(inheritValueMatched)
				{
				    premise_value = true;	
				}
				else if( !inheritVal.isEmpty() && inheritValueMatched == false && nullPresent == false)
				{
					premise_value = false;
				}
				else
				{
					HashMap<String, ArrayList<String>> subsMap = new HashMap<String, ArrayList<String>>();// Map of possible subs values.
					HashMap<String, ArrayList<String>> matchedMap = new HashMap<String, ArrayList<String>>();// Map of possible matched var values which to be put in parents map.
					map.put(premises, false);
					ArrayList<Arg> cargs = qs.arg;
					matchFacts(clauseList,arguments,subsMap,parent,map,cargs,premises,matchedMap,qs);
					if(map.get(premises) == false)
					{
						premise_value = false;
					}
					else
					{
						// Updating parents map with true subs only if its evaluate to true
						ArrayList<Arg> parentArg = tokenClauseMap.get(parent).arg;
						HashMap<String, ArrayList<String>> parentMap = new HashMap<String, ArrayList<String>>();
						for(int t=0;t<arguments.size();t++)
						{
							if(arguments.get(t).value == null )
							{
								if(matchedMap.containsKey(arguments.get(t).var))
								{
									for(Arg parVar : parentArg)
									{
										if(parVar.var.equals(arguments.get(t).var))
										{
											parentMap.put(parVar.var, matchedMap.get(arguments.get(t).var));
										}
										else
										{
											parentMap.put(arguments.get(t).var, matchedMap.get(arguments.get(t).var));
										}
									}
								}
							}
						}								
						tokenClauseMap.get(parent).childMap.putAll(parentMap);
					}
				}
			}
			else if(tokenClauseMap.get(premises) != null && !tokenClauseMap.get(premises).childMap.isEmpty())// Inheriting values from parent.
			{
				HashMap<String, ArrayList<String>> inheritedValues = tokenClauseMap.get(parent).childMap;
				for(String iVar : inheritedValues.keySet())
				{
					for(String iValue:inheritedValues.get(iVar))
					{
						Collection<Arg> dummy_arg = new ArrayList<Arg>();
						for(Arg argu :arguments)
						{
							dummy_arg.add(new Arg(argu.var,argu.isVar,argu.value)); // Deep copying values from Argum to dummy
						}   
						for(Arg dumArg : dummy_arg)
						{
							if(dumArg.var.equals(iVar))
							{
								if(dumArg.value == null)
								{
									dumArg.value = iValue;
								}
							}
						}
						String matchedArgs = "";
						for(int k=0;k<dummy_arg.size();k++)
						{
							if(matchedArgs.isEmpty())
							{
								matchedArgs = matchedArgs + ((ArrayList<Arg>) dummy_arg).get(k).value;
							}
							else
							{
								matchedArgs = matchedArgs + "," + ((ArrayList<Arg>) dummy_arg).get(k).value;
							}
						}
						String matched_value = qs.pred + "(" + matchedArgs + ")";
						if(clauseList.contains(matched_value))
						{
							map.put(premises, true);
							premise_value = true;
						}
					}
				}
			}
			if(clausePresent && map.get(premises) == false) // If it contains Premises
			{
				for(int u=0;u<clause.size();u++)
				{
					for(int j=0;j<clauseMap.get(clause.get(u)).size();j++) // Evaluating Premises of Premise in loop. (2nd level)
					{
						Structure cs = tokenClauseMap.get(clause.get(u));
						ArrayList<Arg> cargs = cs.arg;
						for(int s=0;s<cargs.size();s++)
						{
							cargs.get(s).value = arguments.get(s).value;
						}	
						premise_value = compute_value(clauseMap.get(clause.get(u)).get(j),clause.get(u),cargs,clauseMap,tokenClauseMap,clauseList,queryMap,query,startClause,startQuery);
						if ( premise_value == true)
						{
							return true;
						}
					}
				}
			}			
		}
		return premise_value;
	}

	private static void matchFacts(ArrayList<String> clauseList, ArrayList<Arg> arguments, HashMap<String, ArrayList<String>> subsMap, String parent, HashMap<String, Boolean> map, ArrayList<Arg> carg, String key, HashMap<String, ArrayList<String>> matchedMap, Structure qs) 
	{
		ArrayList<String> matchedFacts = new ArrayList<String>(); // List holding possible facts that can be matched.
		for(int l=0;l<clauseList.size();l++)
		{
			if(clauseList.get(l).startsWith(qs.pred)||clauseList.get(l).startsWith("~" + qs.pred))
			{
				matchedFacts.add(clauseList.get(l));
			}
		}
		for(int w = 0;w<matchedFacts.size();w++)
		{
			Structure mfs = tokenize(matchedFacts.get(w));
			ArrayList<Arg> mfs_arg = mfs.arg;
			Collection<Arg> dummy_arg = new ArrayList<Arg>();
			for(Arg argu :arguments)
			{
				dummy_arg.add(new Arg(argu.var,argu.isVar,argu.value)); // Deep copying values from Argum to dummy
			}

			for(int h=0;h<arguments.size();h++)
			{
				if(!mfs_arg.get(h).var.equals(arguments.get(h).value))
				{
					if(arguments.get(h).value == null) // Substitution changes to be made here.
					{
						((ArrayList<Arg>) dummy_arg).get(h).value = mfs_arg.get(h).var; //Proper code
						if(subsMap.get(((ArrayList<Arg>) dummy_arg).get(h).var) == null)
						{
							subsMap.put(((ArrayList<Arg>) dummy_arg).get(h).var, new ArrayList<String>());
							subsMap.get(((ArrayList<Arg>) dummy_arg).get(h).var).add(((ArrayList<Arg>) dummy_arg).get(h).value);
						}
						else
						{
							subsMap.get(((ArrayList<Arg>) dummy_arg).get(h).var).add(((ArrayList<Arg>) dummy_arg).get(h).value);
						}			
					}
				}
			}
			String matchedArgs = "";
			for(int k=0;k<dummy_arg.size();k++)
			{
				if(matchedArgs.isEmpty())
				{
					matchedArgs = matchedArgs + ((ArrayList<Arg>) dummy_arg).get(k).value;
				}
				else
				{
					matchedArgs = matchedArgs + "," + ((ArrayList<Arg>) dummy_arg).get(k).value;
				}
			}
			String matched_value = qs.pred + "(" + matchedArgs + ")";
			if(clauseList.contains(matched_value))
			{
				for(int u =0;u<dummy_arg.size();u++)
				{
					for(String key1 :subsMap.keySet())
					{
						if(((ArrayList<Arg>) dummy_arg).get(u).var.equals(key1))
						{
							if(matchedMap.get(key1) == null)
							{
								matchedMap.put(key1, new ArrayList<String>());
								matchedMap.get(key1).add(((ArrayList<Arg>) dummy_arg).get(u).value);
							}
							else
							{
								matchedMap.get(key1).add(((ArrayList<Arg>) dummy_arg).get(u).value);
							}
						}
					}

				}
				map.put(key, true);
				for(int j=0;j< tokenClauseMap.get(parent).arg.size();j++)
				{
					if (tokenClauseMap.get(parent).arg.get(j).value == null)
					{
						for(Arg dum:dummy_arg)
						{
							if(tokenClauseMap.get(parent).arg.get(j).var.equals(dum.var))
							{
								tokenClauseMap.get(parent).arg.get(j).value = dum.value;
							}
						}
					}
				}
				carg = tokenClauseMap.get(parent).arg; 
			}
		}

	}

	private static HashMap<String, Structure> tokenize(HashMap<String, ArrayList<String>> clauseMap)
	{
		HashMap<String, Structure> tokenMap = new HashMap<String, Structure>(); // Map of Clauses and Parsed Clauses
		for(String query: clauseMap.keySet())
		{
			Structure qs = new Structure();
			if(query.contains("~"))
			{
				qs.isNegate = true;
				if(query.contains("("))
				{
					Matcher m2 = Pattern.compile("~(.*?)\\(").matcher(query);
					while(m2.find())
					{
						qs.pred = m2.group(1);
					}
				}
				else
				{
					qs.pred = query;
				}
			}
			else
			{
				qs.isNegate = false;
				if(query.contains("("))
				{
					Matcher m2 = Pattern.compile("(.*?)\\(").matcher(query);
					while(m2.find())
					{
						qs.pred = m2.group(1);
					}
				}
				else
				{
					qs.pred = query;
				}
			}	
			qs.arg = new ArrayList<Arg>();
			Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(query);
			while(m.find())
			{
				if(m.group(1).contains(","))
				{
					String[] var = m.group(1).split(",");
					for(int i =0;i<var.length;i++)
					{
						Arg argu = new Arg();
						argu.var = var[i];
						if(var[i].matches("[a-z]+"))
						{
							argu.isVar = true;
						}
						else if(var[i].matches("[A-Z]+"))
						{
							argu.isVar = false;
//							argu.value = var[i];
						}
						qs.arg.add(argu);
					}
				}
				else
				{
					Arg argu = new Arg();
					argu.var = m.group(1);
					if(m.group(1).matches("[a-z]+"))
					{
						argu.isVar = true;
					}
					qs.arg.add(argu);
				}
			}
			tokenMap.put(query, qs);
		}
		return tokenMap;
	}

	private static Structure tokenize(String token)
	{
		Structure qs = new Structure();
		if(token.contains("~"))
		{
			qs.isNegate = true;
			if(token.contains("("))
			{
				Matcher m2 = Pattern.compile("~(.*?)\\(").matcher(token);
				while(m2.find())
				{
					qs.pred = m2.group(1);
				}
			}
			else
			{
				qs.pred = token;
			}
		}
		else
		{
			qs.isNegate = false;
			if(token.contains("("))
			{
				Matcher m2 = Pattern.compile("(.*?)\\(").matcher(token);
				while(m2.find())
				{
					qs.pred = m2.group(1);
				}
			}
			else
			{
				qs.pred = token;
			}
		}	
		qs.arg = new ArrayList<Arg>();
		Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(token);
		while(m.find())
		{
			if(m.group(1).contains(","))
			{
				String[] var = m.group(1).split(",");
				for(int i =0;i<var.length;i++)
				{
					Arg argu = new Arg();
					argu.var = var[i];
					if(var[i].matches("[a-z]+"))
					{
						argu.isVar = true;
					}
					else if(var[i].matches("[A-Z]+[a-z]*"))
					{
						argu.isVar = false;
//						argu.value = argu.var = var[i]; 
					}
					qs.arg.add(argu);
				}
			}
			else
			{
				Arg argu = new Arg();
				argu.var = m.group(1);
				if(m.group(1).matches("[a-z]+"))
				{
					argu.isVar = true;
				}
				qs.arg.add(argu);
			}
		}
		return qs;
	}

	private static HashMap<String, Structure> tokenize_query(LinkedHashMap<String, Boolean> queryMap,String newQuery)
	{
		HashMap<String, Structure> tokenMap = new HashMap<String, Structure>(); // Map of Queries and Parsed Queries
		if(newQuery == null)
		{
			for(String query: queryMap.keySet())
			{
				Structure qs = new Structure();
				if(query.contains("~"))
				{
					qs.isNegate = true;
					if(query.contains("("))
					{
						Matcher m2 = Pattern.compile("~(.*?)\\(").matcher(query);
						while(m2.find())
						{
							qs.pred = m2.group(1);
						}	
					}
					else
					{
						qs.pred = query;
					}

				}
				else
				{
					qs.isNegate = false;
					if(query.contains("("))
					{
						Matcher m2 = Pattern.compile("(.*?)\\(").matcher(query);
						while(m2.find())
						{
							qs.pred = m2.group(1);
						}	
					}
					else
					{
						qs.pred = query;
					}
				}		
				qs.var = new ArrayList<String>();
				Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(query);
				while(m.find())
				{
					if(m.group(1).contains(","))
					{
						String[] var = m.group(1).split(",");
						for(int i =0;i<var.length;i++)
						{
							qs.var.add(var[i]);
						}
					}
					else
					{
						qs.var.add(m.group(1));
					}
				}
				tokenMap.put(query, qs);
			}	
		}
		else
		{
			Structure qs = new Structure();
			if(newQuery.contains("~"))
			{
				qs.isNegate = true;
				if(newQuery.contains("("))
				{
					Matcher m2 = Pattern.compile("~(.*?)\\(").matcher(newQuery);
					while(m2.find())
					{
						qs.pred = m2.group(1);
					}
				}
				else
				{
					qs.pred = newQuery;
				}
			}
			else
			{
				qs.isNegate = false;
				if(newQuery.contains("("))
				{
					Matcher m2 = Pattern.compile("(.*?)\\(").matcher(newQuery);
					while(m2.find())
					{
						qs.pred = m2.group(1);
					}
				}
				else
				{
					qs.pred = newQuery;
				}
			}		
			qs.var = new ArrayList<String>();
			Matcher m = Pattern.compile("\\(([^)]+)\\)").matcher(newQuery);
			while(m.find())
			{
				if(m.group(1).contains(","))
				{
					String[] var = m.group(1).split(",");
					for(int i =0;i<var.length;i++)
					{
						qs.var.add(var[i]);
					}
				}
				else
				{
					qs.var.add(m.group(1));
				}
			}
			tokenMap.put(newQuery, qs);
		}
		return tokenMap;
	}
	
	public static HashMap<String, ArrayList<String>> copy(HashMap<String, ArrayList<String>> original)
	{
		HashMap<String, ArrayList<String>> copy = new HashMap<String, ArrayList<String>>();
		for (Map.Entry<String, ArrayList<String>> entry : original.entrySet())
		{
			copy.put(entry.getKey(),
					// Or whatever List implementation you'd like here.
					new ArrayList<String>(entry.getValue()));
		}
		return copy;
	}
	
	private static void GeneratePermutations(ArrayList<ArrayList<String>> Lists, int depth, String current,ArrayList<HashMap<String, String>> resultMap,ArrayList<String> keys)
	{
	    if(depth == Lists.size())
	    {
	       String[] values = current.split(" ");
	       HashMap<String, String> localMap = new HashMap<String, String>();
	       for(int i = 0;i<keys.size();i++)
	       {
	    	   localMap.put(keys.get(i), values[i]);
	       }
	       resultMap.add(localMap);
	       return;
	     }

	    for(int i = 0; i < Lists.get(depth).size(); ++i)
	    {
	    	if(current != "")
	            GeneratePermutations(Lists, depth + 1, current + " " + Lists.get(depth).get(i),resultMap,keys);
	    	else
	    		GeneratePermutations(Lists, depth + 1, Lists.get(depth).get(i),resultMap,keys);	
	    }
	}

	public static void main(String[] args) 
	{
		BufferedWriter writer = null;
		try
		{
			File file = new File("output.txt");
			writer = new BufferedWriter(new FileWriter(file));
			LinkedHashMap<String,Boolean> queryMap = read_input_file(args);
			write_output_file(queryMap,writer);
		}
		catch ( IOException e )
		{
			e.printStackTrace();
		} 
		finally 
		{
			if ( writer != null )
				try 
			{
					writer.close();
			}
			catch (IOException e)
			{
				e.printStackTrace();
			}
		}
	}

	private static void write_output_file(LinkedHashMap<String, Boolean> queryMap, BufferedWriter writer)
	{
		for(Boolean value : queryMap.values())
		{
			try
			{
				if(value)
				{
					writer.write(TRUE);
				}   
				else
				{
					writer.write(FALSE);
				}
			}
			catch(IOException e)
			{
				e.printStackTrace();
			}
			finally
			{

			}
		}
	}
}
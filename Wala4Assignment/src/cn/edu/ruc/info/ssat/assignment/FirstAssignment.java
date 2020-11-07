package cn.edu.ruc.info.ssat.assignment;

import com.ibm.wala.cfg.ControlFlowGraph;
import com.ibm.wala.classLoader.Language;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.SSAPropagationCallGraphBuilder;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.Iterator2Iterable;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.ssa.*;
import com.ibm.wala.viz.DotUtil;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.jar.JarFile;

public class FirstAssignment {
	private static final ClassLoader WALA_CLASSLOADER = AnalysisScopeReader.class.getClassLoader();
	private static final String BASIC_FILE = "res/primordial.txt";
	private static final String STD_JAR = "res/android.jar";
	private static final String EXCLUSION_FILE = "res/Java60RegressionExclusions.txt";
	// change the target jar file address for other test case addresses
	private static final String TARGET = "tests/Test4FirstAssignment.jar";

	private ClassHierarchy cha;
	private CallGraph cg;
	private Set<CGNode> cgnode_set = new HashSet<CGNode>();

	public static void main(String[] args) throws WalaException {
		FirstAssignment fa = new FirstAssignment();
		fa.doAnalysis();
	}

	public FirstAssignment() {

	}

	private void initialize() throws IOException, ClassHierarchyException, CallGraphBuilderCancelException {
		// initialize a basic analysis scope
		AnalysisScope scope = AnalysisScopeReader.readJavaScope(BASIC_FILE, new File(EXCLUSION_FILE), WALA_CLASSLOADER);
		// add the std lib (use android.jar here) into the analysis scope
		scope.addToScope(ClassLoaderReference.Primordial, new JarFile(STD_JAR));
		// add the target application into the scope
		scope.addToScope(ClassLoaderReference.Application, new JarFile(TARGET));
		// build the class hierarchy
		cha = ClassHierarchyFactory.make(scope);
		// find the entrypoint, i.e., main()
		Iterable<Entrypoint> entrypoints = Util.makeMainEntrypoints(scope, cha);
		// build the call graph
		AnalysisOptions options = new AnalysisOptions(scope, entrypoints);
		// you can change the "makeZeroCFABuilder" call to other available methods to see the differences
		SSAPropagationCallGraphBuilder cgBuilder = Util.makeZeroCFABuilder(Language.JAVA, options,
																		   new AnalysisCacheImpl(), cha, scope);
		cg = cgBuilder.makeCallGraph(options, null);
	}

	public void doAnalysis() throws WalaException {
		try {
			initialize();
		} catch (Exception e) {
			e.printStackTrace();
			System.exit(0);
		}

		/*****************start your code here*****************/
//		System.out.println(cg.getEntrypointNodes().stream().findFirst().get().getIR());
//		System.out.println(cg.getFakeRootNode());

		CG_DFS(cg.getFakeRootNode(), 0);

/*
		for (CGNode cn : cg) {

			System.out.println(cn);
			// the code below print all instructions of a call graph node (cfg)
//			IR ir = cn.getIR();
//			if (ir==null) continue;
//			SSAInstruction[] instructions = ir.getInstructions();
//			for (int start = 0; start < instructions.length; start++) System.out.println(instructions[start]);

			// test dfs on cfg
			ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg = cn.getIR().getControlFlowGraph();
//			Set<ISSABasicBlock> bbset = new HashSet<ISSABasicBlock>();
//			CFG_DFS(bbset, cfg.getNode(0),0,cfg);

			// the code below print the instructions of each bb in cfg
			for (ISSABasicBlock basicBlock: cfg){
				System.out.println(basicBlock);
				for(int start=basicBlock.getFirstInstructionIndex(); start <= basicBlock.getLastInstructionIndex(); start++){
					System.out.println(cfg.getInstructions()[start]);
				}
			}
			System.out.println();
		}

*/
		String DOT_EXE="D:\\Graphviz 2.44.1\\bin\\dot";
		String DOT_FILE="temp.dt";
		String PDF_FILE="temp.pdf";

		DotUtil.dotify(cg, null, DOT_FILE, PDF_FILE, DOT_EXE);
	}

	public int CG_DFS(CGNode current_node, int level) throws WalaException {

		/*
			This function do dfs search on call graph, and should be invoked after initialize.
			User can invoke it in doAnalysis function after the try... catch... statements.
			Besides, this function also invokes CFG_DFS and do DFS on CFG of each node in CG.
		 */
		// ensure that current node has not been visited
		if (cgnode_set.contains(current_node)){
				return 0;
		}
		// print information of current node
		System.out.println("level" + String.format("%-3d",level) + ":" +
				String.join("", Collections.nCopies(level,"\t")) + current_node.toString());
		// do cfg dfs for each node in cg
		Set<ISSABasicBlock> bbset = new HashSet<ISSABasicBlock>();
		ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg = current_node.getIR().getControlFlowGraph();
		CFG_DFS(bbset, cfg.getNode(0), level+1, cfg);

		//dfs: search unvisited sons
		cgnode_set.add(current_node);
		for (CGNode cn: Iterator2Iterable.make(cg.getSuccNodes(current_node))){
			CG_DFS(cn, level+1);
		}
		cgnode_set.remove(current_node);
		return 0;
	}

	public int CFG_DFS(Set<ISSABasicBlock> bb_set, ISSABasicBlock basicBlock, int level, ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg){

		/* this function is used to do dfs on cfg, and print the information basic block and the instructions*/
		//
		if (bb_set.contains(basicBlock)){
			return 0;
		}
		// print information and instructions of the basic block
		SSAInstruction[] instructions = cfg.getInstructions();
		System.out.println("level" + String.format("%-3d",level) + ":" +
				String.join("", Collections.nCopies(level,"\t")) +"BB:\t"+basicBlock);
		for(int start=basicBlock.getFirstInstructionIndex(); start <= basicBlock.getLastInstructionIndex(); start++){
			System.out.println("level" + String.format("%-3d",level+1) + ":" +
					String.join("", Collections.nCopies(level+1,"\t")) + "Instructions:\t" + instructions[start]);
		}
		// search the unvisited sons
		bb_set.add(basicBlock);
		for (ISSABasicBlock b: Iterator2Iterable.make(cfg.getSuccNodes(basicBlock))){
			CFG_DFS(bb_set,b,level+1,cfg);
		}
		bb_set.remove(basicBlock);
		return 0;
	}

}

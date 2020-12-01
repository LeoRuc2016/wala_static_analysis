package cn.edu.ruc.info.ssat.assignment;

import com.ibm.wala.cfg.ControlFlowGraph;
import com.ibm.wala.classLoader.*;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.SSAPropagationCallGraphBuilder;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.ipa.slicer.*;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.Descriptor;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.Iterator2Iterable;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.ssa.*;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.GraphIntegrity;
import com.ibm.wala.util.graph.traverse.DFS;
import com.ibm.wala.util.strings.Atom;
import com.ibm.wala.viz.DotUtil;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.modref.ModRef;
import com.ibm.wala.cast.ipa.callgraph.AstSSAPropagationCallGraphBuilder;
import com.ibm.wala.cast.tree.CAstSourcePositionMap.Position;
import com.ibm.wala.cast.util.SourceBuffer;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.NonNullSingletonIterator;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.graph.traverse.DFSPathFinder;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
//import com.sun.org.apache.xpath.internal.operations.String;

import java.io.*;
import java.util.*;
import java.util.jar.JarFile;


public class FirstAssignment{
	private static final ClassLoader WALA_CLASSLOADER = AnalysisScopeReader.class.getClassLoader();
	private static final String BASIC_FILE = "res/primordial.txt";
	private static final String STD_JAR = "res/android.jar";
	private static final String EXCLUSION_FILE = "res/Java60RegressionExclusions.txt";
	// change the target jar file address for other test case addresses
	private static final String TARGET = "tests/Test4FirstAssignment.jar";

	private ClassHierarchy cha;
	private CallGraph cg;
	private Graph<Statement> sdg;
	private Set<CGNode> cgnode_set = new HashSet<CGNode>();
	
	private String[] source;
	private int source_num;
	private String[] sink;
	private int sink_num;
	private Object BufferedReader;

	public int[] taint_reg;
	public int taint_num;
	public IMethod[] method_names;
	public Descriptor[] descriptors;
	public IClass[] clas;
	public int[] lifeofreg;
	public IField[] taint_field;
	public int taint_field_num;

	public ArrayList<SSAInstruction> ins_path = new ArrayList<SSAInstruction>();


	public static void main(String[] args) throws WalaException, FileNotFoundException {
		FirstAssignment fa = new FirstAssignment();
		fa.doAnalysis();
	}

	public FirstAssignment() {

	}

	public int ifFieldStain(IField field) {
		for(int i=0;i < taint_field_num;i++) {
			if(field.equals(taint_field[i])) {
				return i;
			}
		}
		return -1;
	}

	public int ifRegStain(int v,IMethod method,IClass cla) {
		for(int i=0;i<taint_num;i++) {
			if(taint_reg[i]==v && method_names[i]==method && clas[i]==cla) {
				return i;
			}
		}
		return -1;
	}

	public void AddStainRegister(int str,IMethod method,Descriptor des,int line,IClass cla) {
		//System.out.println("regadd"+str+method+cla);
		for(int i=0;i<taint_num;i++)
		{
			if(taint_reg[i]==str&&method_names[i]==method&&clas[i]==cla)
			{
				return;
			}
		}

		if(taint_reg.length==taint_num)
		{
			taint_reg=Arrays.copyOf(taint_reg, taint_reg.length+10);
			method_names=Arrays.copyOf(method_names, method_names.length+10);
			clas=Arrays.copyOf(clas, clas.length+10);
			lifeofreg=Arrays.copyOf(lifeofreg, lifeofreg.length+10);
			descriptors=Arrays.copyOf(descriptors, descriptors.length+10);

		}
		taint_reg[taint_num]=str;
		method_names[taint_num]=method;
		descriptors[taint_num]=des;
		lifeofreg[taint_num]=line;
		clas[taint_num]=cla;
		taint_num++;

	}
	public void AddStainField(IField field) {


		for(int i=0;i<taint_field_num;i++) {
			if(field==taint_field[i]) {
				return;
			}
		}
		if(taint_field.length==taint_field_num) {
			taint_field=Arrays.copyOf(taint_field, taint_field.length+10);
		}
		taint_field[taint_field_num]=field;
		taint_field_num++;
	}

	private void init_source_sink(String filepath) throws FileNotFoundException {

		source=new String[1];
		source_num=0;

		sink=new String[1];
		sink_num=0;
		
		try (FileReader reader = new FileReader(filepath); BufferedReader br = new BufferedReader(reader)){
			
			String line;

			while ((line = br.readLine()) != null) {
//				System.out.println(line);
				if(line.split(" ")[0].equals("SOURCE")) {

					if(source_num==source.length){
						source = Arrays.copyOf(source, source.length+1);
					}
					source[source_num] = line.split(" ")[1];
					source_num++;
				}else if(line.split(" ")[0].equals("SINK")) {

					if (sink_num == sink.length){
						sink = Arrays.copyOf(sink, sink.length+10);
					}
					sink[sink_num] = line.split(" ")[1];
					sink_num++;
				}
			}

		} catch (IOException e) {
			e.printStackTrace();
		}

	}

	public boolean ifsource(String sig)
	{
		for(int i=0;i<source_num;i++)
			if(sig.equals(source[i]))
				return true;
		return false;
	}

	public boolean ifsink(String sig)
	{
		for(int i=0;i<sink_num;i++)
			if(sig.equals(sink[i]))
				return true;
		return false;
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
//		cha.getPo
//		System.out.println(cha);
		// find the entrypoint, i.e., main()
		Iterable<Entrypoint> entrypoints = Util.makeMainEntrypoints(scope, cha);
		// build the call graph
		AnalysisOptions options = new AnalysisOptions(scope, entrypoints);
		// you can change the "makeZeroCFABuilder" call to other available methods to see the differences
		SSAPropagationCallGraphBuilder cgBuilder = Util.makeZeroCFABuilder(Language.JAVA, options,
																		   new AnalysisCacheImpl(), cha, scope);
		cg = cgBuilder.makeCallGraph(options, null);

		final PointerAnalysis<InstanceKey> pointerAnalysis = cgBuilder.getPointerAnalysis();
		sdg = new SDG<>(cg, pointerAnalysis, DataDependenceOptions.NO_BASE_NO_HEAP_NO_EXCEPTIONS, ControlDependenceOptions.NONE);


	}

	public void doAnalysis() throws WalaException, FileNotFoundException {
		try {
			initialize();
		} catch (Exception e) {
			e.printStackTrace();
			System.exit(0);
		}

		try{
			GraphIntegrity.check(sdg);
		} catch(GraphIntegrity.UnsoundGraphException e1){
			e1.printStackTrace();
			Assertions.UNREACHABLE();
		}

		/*****************start your code here*****************/
//		System.out.println(cg.getEntrypointNodes().stream().findFirst().get().getIR());
//		System.out.println(cg.getFakeRootNode());
//		System.out.println(sdg);

		String filepath = "sourcesink.txt";
		init_source_sink(filepath);
//		System.out.println(source[0]);
//		System.out.println(sink[0]);

		CGNode main_point = null;
		Descriptor d = Descriptor.findOrCreateUTF8("([Ljava/lang/String;)V");
		Atom name = Atom.findOrCreateUnicodeAtom("main");
		for (Iterator<? extends CGNode> it = cg.getSuccNodes(cg.getFakeRootNode()); it.hasNext();) {
			CGNode n = it.next();
			if (n.getMethod().getName().equals(name) && n.getMethod().getDescriptor().equals(d)) {
				main_point = n;
				break;
			}
		}
		if (main_point == null)
			return;

//		IR ir = main_point.getIR();
//		isTaint =new int[cg.getMaxNumber()+1][ir.getControlFlowGraph().getMaxNumber()+401];
//		for(int i=0;i<=ir.getControlFlowGraph().getMaxNumber()+400;i++)
//			for(int j=0;j<=cg.getMaxNumber();j++)
//				isTaint[j][i]=0;

		taint_reg = new int[1];
		method_names = new IMethod[1];
		descriptors = new Descriptor[1];
		taint_num = 0;
		lifeofreg = new int[1];
		clas = new IClass[1];
		taint_field = new IField[1];
		taint_field_num = 0;


		CG_DFS(main_point, 0);

//	int count = 0;
//	System.out.println(cg.getNumberOfNodes());
//	for (CGNode cn : cg) {
//
//			// the code below print all instructions of a call graph node (cfg)
//			IR ir = cn.getIR();
//			count++;
//			System.out.println("node" + count +": "+ cn.getMethod().toString());
//			SSAInstruction[] instructions = ir.getInstructions();
//			for (int start = 0; start < instructions.length; start++) System.out.println(instructions[start]);
//			for (int i = 0; i < ir.getSymbolTable().getMaxValueNumber(); i++)
//			if (cn.getKind()== Statement.Kind.NORMAL)
//				if(((NormalStatement)cn).getInstruction() instanceof SSAGetInstruction)
//					System.out.println(((SSAGetInstruction)((NormalStatement) cn).getInstruction()).getDeclaredField().getName().toString());

//			System.out.println();
//			if (ir==null) continue;


			// test dfs on cfg
			//ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg = cn.getIR().getControlFlowGraph();
//			Set<ISSABasicBlock> bbset = new HashSet<ISSABasicBlock>();
//			CFG_DFS(bbset, cfg.getNode(0),0,cfg);
			// the code below print the instructions of each bb in cfg
/*
			for (ISSABasicBlock basicBlock: cfg){
				System.out.println(basicBlock.getLastInstruction());
				//for(int start=basicBlock.getFirstInstructionIndex(); start <= basicBlock.getLastInstructionIndex(); start++){
				//	System.out.println(cfg.getInstructions()[start]);
				//}
				if (basicBlock.getLastInstruction() instanceof SSAInvokeInstruction){

					final int numParams = ((SSAInvokeInstruction) basicBlock.getLastInstruction()).getNumberOfPositionalParameters();
					for (int i = 0; i < numParams; i++) {
						basicBlock.getLastInstruction().getUse(i);
					}
				}
			}
*/

		//	System.out.println();
		//}


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
//		System.out.println("level" + String.format("%-3d",level) + ":" +
//				String.join("", Collections.nCopies(level,"\t")) + current_node.toString());
		// do cfg dfs for each node in cg
		HashMap<ISSABasicBlock, Integer> bbset = new HashMap<ISSABasicBlock, Integer>();
		ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg = current_node.getIR().getControlFlowGraph();
		CFG_DFS(bbset, current_node.getIR().getBlocks().next(), level+1, cfg);

		//dfs: search unvisited sons
//		cgnode_set.add(current_node);
//		for (CGNode cn: Iterator2Iterable.make(cg.getSuccNodes(current_node))){
//			CG_DFS(cn, level+1);
//		}
//		cgnode_set.remove(current_node);
		return 0;
	}
	public int[] taint_reg_copy;
	public int taint_num_copy;
	public IMethod[] method_names_copy;
	public Descriptor[] descriptors_copy;
	public IClass[] clas_copy;
	public int[] lifeofreg_copy;
	public IField[] taint_field_copy;
	public int taint_field_num_copy;
	public void copy(){

		taint_reg_copy = taint_reg;
		taint_num_copy = taint_num;
		taint_field_num_copy = taint_field_num;
		method_names_copy = method_names;
		descriptors_copy = descriptors;
		clas_copy = clas;
		lifeofreg_copy = lifeofreg;
		taint_field_copy = taint_field;
	}

	public void reverse(){

		taint_reg = taint_reg_copy;
		taint_num = taint_num_copy;
		taint_field_num = taint_field_num_copy;
		method_names = method_names_copy;
		descriptors = descriptors_copy;
		clas = clas_copy;
		lifeofreg = lifeofreg_copy;
		taint_field = taint_field_copy;

	}

	public int CFG_DFS(HashMap<ISSABasicBlock, Integer> bb_set, ISSABasicBlock basicBlock, int level, ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg){

		/* this function is used to do dfs on cfg, and print the information basic block and the instructions*/
		//
//		if (bb_set.contains(basicBlock)){
//			return 0;
//		}
		// print information and instructions of the basic block
//		SSAInstruction[] instructions_ = cfg.getInstructions();
//		System.out.println("level" + String.format("%-3d",level) + ":" +
//				String.join("", Collections.nCopies(level,"\t")) +"BB:\t"+basicBlock);
//		for(int start=basicBlock.getFirstInstructionIndex(); start <= basicBlock.getLastInstructionIndex(); start++){
//			System.out.println("level" + String.format("%-3d",level+1) + ":" +
//					String.join("", Collections.nCopies(level+1,"\t")) + "Instructions:\t" + instructions_[start]);
//		}
		// search the unvisited sons

		int count = 0;
		for (Iterator<SSAInstruction> instructions = basicBlock.iterator(); instructions.hasNext();){

			SSAInstruction ins = instructions.next();
			ins_path.add(ins);
			count++;
//			System.out.println(ins);

			if (ins instanceof com.ibm.wala.ssa.SSAReturnInstruction){

				com.ibm.wala.ssa.SSAReturnInstruction ret=(com.ibm.wala.ssa.SSAReturnInstruction) ins;
				if(ifRegStain(ret.getUse(0), basicBlock.getMethod(), basicBlock.getMethod().getDeclaringClass())!=-1)
				{
					return 1;
				}
			}

			if(ins  instanceof com.ibm.wala.ssa.SSAPutInstruction) {
				IField ifield=cha.resolveField(((com.ibm.wala.ssa.SSAPutInstruction) ins).getDeclaredField());
				for(int i=0;i<ins.getNumberOfUses();i++)
					if(ifRegStain(ins.getUse(i), basicBlock.getMethod(), basicBlock.getMethod().getDeclaringClass())!=-1){
						AddStainField(ifield);
					}
			}

			if(ins  instanceof com.ibm.wala.ssa.SSAGetInstruction) {
				com.ibm.wala.ssa.SSAGetInstruction get =(com.ibm.wala.ssa.SSAGetInstruction) ins;
				IField ifield=cha.resolveField(((com.ibm.wala.ssa.SSAGetInstruction) ins).getDeclaredField());
				if(ifFieldStain(ifield)!=-1) {
					AddStainRegister(get.getDef(), cfg.getMethod(), cfg.getMethod().getDescriptor(), basicBlock.getMethod().getLineNumber(ins.iindex) , cfg.getMethod().getDeclaringClass());
				}

			}

			if(ins  instanceof com.ibm.wala.ssa.SSABinaryOpInstruction) {
				com.ibm.wala.ssa.SSABinaryOpInstruction op = (com.ibm.wala.ssa.SSABinaryOpInstruction) ins;
				int i=ifRegStain(op.getUse(0),cfg.getMethod(),cfg.getMethod().getDeclaringClass());
				if(i!=-1) {
					AddStainRegister(op.getDef(), cfg.getMethod(), cfg.getMethod().getDescriptor(), basicBlock.getMethod().getLineNumber(op.iindex), cfg.getMethod().getDeclaringClass());
				}
				i=ifRegStain(op.getUse(1),cfg.getMethod(),cfg.getMethod().getDeclaringClass());
				if(i!=-1) {
					AddStainRegister(op.getDef(), cfg.getMethod(), cfg.getMethod().getDescriptor(), basicBlock.getMethod().getLineNumber(op.iindex), cfg.getMethod().getDeclaringClass());
				}
			}

			if(ins  instanceof com.ibm.wala.ssa.SSAAbstractInvokeInstruction) {
				com.ibm.wala.ssa.SSAAbstractInvokeInstruction call = (com.ibm.wala.ssa.SSAAbstractInvokeInstruction) ins;

//				System.out.println("getuse: " + call.getNumberOfUses());
//				for (int i=0; i < call.getNumberOfUses();i++){
//					System.out.println(call.getUse(i));
//
//				}

				if(ifsource(call.getCallSite().getDeclaredTarget().getSignature())) {
					System.out.print("source:class:"+cfg.getMethod().getDeclaringClass()+",method:"+basicBlock.getMethod().toString());
					AddStainRegister(call.getDef(),basicBlock.getMethod(), basicBlock.getMethod().getDescriptor(), basicBlock.getMethod().getLineNumber(call.getProgramCounter()),basicBlock.getMethod().getDeclaringClass() );
//					System.out.println("level" + String.format("%-3d",level+1) + ":" + String.join("", Collections.nCopies(level+1,"\t")) + "Instructions:\t" + instructions[start]);
					System.out.println("line"+basicBlock.getMethod().getLineNumber(call.getProgramCounter()));
				}
				//sink点
				if(ifsink(call.getCallSite().getDeclaredTarget().getSignature())) {
					System.out.println("find sink:"+call.getCallSite().getDeclaredTarget().getSignature());
					System.out.println("Path:");
					for (int i = 0; i < ins_path.size(); i++){
						System.out.println("\t" + ins_path.get(i));
					}

					for (int i = 0; i < taint_reg.length; i++){
						System.out.println(taint_reg[i]);
					}

					for(int i=0;i<taint_num;i++) {
						if(taint_reg[i]==call.getUse(1)) {
							//System.out.println("source:\nclass:"+sd.clas[i]+",method:"+sd.MethodNames[i].toString()+",line:"+sd.LineofRegister[i]);
							System.out.println("find taint spread path from source to sink!");
							int sinkline=basicBlock.getMethod().getLineNumber(call.getProgramCounter());
							System.out.println("sink:class:"+cfg.getMethod().getDeclaringClass()+",method:"+basicBlock.getMethod().toString()+",line:"+sinkline);
						}
					}
				}

				AddStainRegister(call.getDef(0), basicBlock.getMethod(), basicBlock.getMethod().getDescriptor(), 1, basicBlock.getMethod().getDeclaringClass());

				for (Iterator<? extends CGNode> it = cg.iterator(); it.hasNext();) {
					CGNode n = it.next();
					if (n.getMethod().getDescriptor().equals(call.getCallSite().getDeclaredTarget().getDescriptor()) &&
							n.getMethod().getName().equals(call.getCallSite().getDeclaredTarget().getName())) {

						for(int s=0;s<n.getIR().getNumberOfParameters();s++)
							if(ifRegStain(ins.getUse(s),basicBlock.getMethod(),basicBlock.getMethod().getDeclaringClass())!=-1)
								AddStainRegister(n.getIR().getParameter(s),cha.resolveMethod(call.getCallSite().getDeclaredTarget()),cha.resolveMethod(call.getCallSite().getDeclaredTarget()).getDescriptor(), basicBlock.getMethod().getLineNumber(call.getProgramCounter()),cha.resolveMethod(call.getCallSite().getDeclaredTarget()).getDeclaringClass());

						if (n!=null && bb_set.get(basicBlock)<=3 && n.getIR()!=null) {
							if (!bb_set.containsKey(n.getIR().getBlocks().next()))bb_set.put(n.getIR().getBlocks().next(),0);
							else bb_set.put(n.getIR().getBlocks().next(), bb_set.get( n.getIR().getBlocks().next())+1);
							copy();
							if (1 == CFG_DFS(bb_set, n.getIR().getBlocks().next(), level + 1, n.getIR().getControlFlowGraph())) {
								AddStainRegister(call.getDef(0), basicBlock.getMethod(), basicBlock.getMethod().getDescriptor(), 1, basicBlock.getMethod().getDeclaringClass());
							}
							bb_set.put(n.getIR().getBlocks().next(), bb_set.get(n.getIR().getBlocks().next())-1);
							reverse();
						}
					}
				}
				//Assertions.UNREACHABLE("Failed to find method " + name);
			}
		}


		for (ISSABasicBlock b: Iterator2Iterable.make(cfg.getSuccNodes(basicBlock))){

			copy();
			if (!bb_set.containsKey(b))bb_set.put(b,0);
			else bb_set.put(b, bb_set.get(b)+1);
			CFG_DFS(bb_set,b,level+1,cfg);
			bb_set.put(b, bb_set.get(b)+1);
			reverse();
		}

		for (;count>0; count--){

			ins_path.remove(ins_path.size()-1);
		}

//		bb_set.add(basicBlock);

//		bb_set.remove(basicBlock);
		return 0;
	}

}

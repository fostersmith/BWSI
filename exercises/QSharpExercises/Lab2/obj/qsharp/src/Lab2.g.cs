//------------------------------------------------------------------------------
// <auto-generated>                                                             
//     This code was generated by a tool.                                       
//     Changes to this file may cause incorrect behavior and will be lost if    
//     the code is regenerated.                                                 
// </auto-generated>                                                            
//------------------------------------------------------------------------------
#pragma warning disable 436
#pragma warning disable 162
#pragma warning disable 1591
using System;
using Microsoft.Quantum.Core;
using Microsoft.Quantum.Intrinsic;
using Microsoft.Quantum.Intrinsic.Interfaces;
using Microsoft.Quantum.Simulation.Core;

[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise1\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Opaque\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Empty\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":32,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"qubitA\"]},\"Type\":{\"Case\":\"Qubit\"},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":22},\"Item2\":{\"Line\":1,\"Column\":28}}}]},{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"qubitB\"]},\"Type\":{\"Case\":\"Qubit\"},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":38},\"Item2\":{\"Line\":1,\"Column\":44}}}]}]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"Qubit\"},{\"Case\":\"Qubit\"}]]},\"ReturnType\":{\"Case\":\"UnitType\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[\" # Summary\",\" In this exercise, you are given two qubits. Both qubits are in\",\" arbitrary, unknown states:\",\"\",\"     |QubitA> = a|0> + b|1>\",\"     |QubitB> = c|0> + d|1>\",\"\",\" Use the two-qubit gates in Q# to switch their amplitudes, so\",\" this is the end result:\",\"\",\"     |QubitA> = c|0> + d|1>\",\"     |QubitB> = a|0> + b|1>\",\"\",\" # Input\",\" ## qubitA\",\" The first qubit, which starts in the state a|0> + b|1>.\",\"\",\" ## qubitB\",\" The second qubit, which starts in the state c|0> + d|1>.\",\"\",\" # Remarks\",\" This will show you how to apply quantum gates that take more than one\",\" qubit.\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise1\"},\"Attributes\":[],\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":32,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"Documentation\":[]}")]
[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise2\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Opaque\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Empty\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":71,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"register\"]},\"Type\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Qubit\"}]},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":22},\"Item2\":{\"Line\":1,\"Column\":30}}}]}]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Qubit\"}]},\"ReturnType\":{\"Case\":\"UnitType\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[\" # Summary\",\" In this exercise, you're given a register of qubits with unknown\",\" length. Each qubit is in an arbitrary, unknown state. Your goal\",\" is to reverse the register, so the order of qubits is reversed.\",\"\",\" For example, if the register had 3 qubits where:\",\"\",\"     |Q0> = a|0> + b|1>\",\"     |Q1> = c|0> + d|1>\",\"     |Q2> = e|0> + f|1>\",\"\",\" Your goal would be to modify the qubits in the register so that\",\" the qubit's states are reversed:\",\"\",\"     |Q0> = e|0> + f|1>\",\"     |Q1> = c|0> + d|1>\",\"     |Q2> = a|0> + b|1>\",\"\",\" Note that the register itself is immutable, so you can't just reorder\",\" the elements like you would in a classical array. In other words, the\",\" first element of the array will always be Q0 and the last element will\",\" always be Q(n-1) - you can't set the first element to Q(n-1) and the\",\" last element to Q0. You must reverse the register by reversing the states\",\" of the qubits themselves, without changing the actual order of the qubits\",\" in the register.\",\"\",\" # Input\",\" ## register\",\" The qubit register that you need to reverse.\",\"\",\" # Remarks\",\" This will test your combined knowledge of arrays and multi-qubit gates.\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise2\"},\"Attributes\":[],\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":71,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"Documentation\":[]}")]
[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise3\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Opaque\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Empty\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":110,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"registers\"]},\"Type\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Qubit\"}]}]},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":22},\"Item2\":{\"Line\":1,\"Column\":31}}}]}]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Qubit\"}]}]},\"ReturnType\":{\"Case\":\"UnitType\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[\" # Summary\",\" In this exercise, you are given an array of qubit registers. There are\",\" four registers in the array, and each register contains two qubits. All\",\" eight qubits will be in the |0> state, so each register is in the state\",\" |00>.\",\"\",\" Your goal is to put the four registers into these four states:\",\"\",\"     Register 0 = 1/√2(|00> + |11>)\",\"     Register 1 = 1/√2(|00> - |11>)\",\"     Register 2 = 1/√2(|01> + |10>)\",\"     Register 3 = 1/√2(|01> - |10>)\",\"\",\" These four states are known as the Bell States. They are the simplest\",\" examples of full entanglement between two qubits.\",\"\",\" # Input\",\" ## registers\",\" An array of four two-qubit registers. All of the qubits are in the |0>\",\" state.\",\"\",\" # Remarks\",\" This will show you how to call quantum operations from other quantum\",\" operations. It will also test your understanding of how register\",\" superposition notation corresponds to the effects that quantum gates\",\" have on qubits.\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise3\"},\"Attributes\":[],\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":110,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"Documentation\":[]}")]
[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise4\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Opaque\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Empty\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":154,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"register\"]},\"Type\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Qubit\"}]},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":22},\"Item2\":{\"Line\":1,\"Column\":30}}}]}]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Qubit\"}]},\"ReturnType\":{\"Case\":\"UnitType\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[\" # Summary\",\" In this exercise, you are given a qubit register of unknown length.\",\" All of the qubits in it are in the |0> state, so the whole register\",\" is in the state |0...0>.\",\"\",\" Your task is to transform this register into this state:\",\"\",\"     |register> = 1/√2(|0...0> + |1...1>)\",\"\",\" For example, if the register had 5 qubits, you would need to put it\",\" in the state 1/√2(|00000> + |11111>). These states are called the\",\" GHZ states.\",\"\",\" # Input\",\" ## register\",\" The qubit register. It is in the state |0...0>.\",\"\",\" # Remarks\",\" This will test your understanding of the relationships between entangled\",\" qubits in a register by making you apply your knowledge to a register\",\" with more than two qubits.\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise4\"},\"Attributes\":[],\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":154,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"Documentation\":[]}")]
[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise5\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Opaque\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Empty\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":177,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[{\"Case\":\"QsTupleItem\",\"Fields\":[{\"VariableName\":{\"Case\":\"ValidName\",\"Fields\":[\"register\"]},\"Type\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Qubit\"}]},\"InferredInformation\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Position\":{\"Case\":\"Null\"},\"Range\":{\"Item1\":{\"Line\":1,\"Column\":22},\"Item2\":{\"Line\":1,\"Column\":30}}}]}]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"ArrayType\",\"Fields\":[{\"Case\":\"Qubit\"}]},\"ReturnType\":{\"Case\":\"UnitType\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[\" # Summary\",\" In this exercise, you are given a qubit register of length four. All of\",\" its qubits are in the |0> state initially, so the whole register is in\",\" the state |0000>.\",\" Your goal is to put it into the following state:\",\"\",\"     |register> = 1/√2(|0101> - |0110>)\",\"\",\" You will need to use the H, X, Z, and CNOT gates to achieve this.\",\"\",\" # Input\",\" ## register\",\" The qubit register. It is in the state |00000>.\"]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"Lab2\",\"Name\":\"Exercise5\"},\"Attributes\":[],\"SourceFile\":\"D:\\\\BWSI\\\\exercises\\\\exercises\\\\QSharpExercises\\\\Lab2\\\\Lab2.qs\",\"Position\":{\"Item1\":177,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":20}},\"Documentation\":[]}")]
#line hidden
namespace Lab2
{
    [SourceLocation("D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs", OperationFunctor.Body, 33, 72)]
    public partial class Exercise1 : Operation<(Qubit,Qubit), QVoid>, ICallable
    {
        public Exercise1(IOperationFactory m) : base(m)
        {
        }

        public class In : QTuple<(Qubit,Qubit)>, IApplyData
        {
            public In((Qubit,Qubit) data) : base(data)
            {
            }

            System.Collections.Generic.IEnumerable<Qubit> IApplyData.Qubits
            {
                get
                {
                    yield return Data.Item1;
                    yield return Data.Item2;
                }
            }
        }

        String ICallable.Name => "Exercise1";
        String ICallable.FullName => "Lab2.Exercise1";
        protected IUnitary<(Qubit,Qubit)> Microsoft__Quantum__Intrinsic__SWAP
        {
            get;
            set;
        }

        public override Func<(Qubit,Qubit), QVoid> __Body__ => (__in__) =>
        {
            var (qubitA,qubitB) = __in__;
#line 36 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Intrinsic__SWAP.Apply((qubitA, qubitB));
#line hidden
            return QVoid.Instance;
        }

        ;
        public override void __Init__()
        {
            this.Microsoft__Quantum__Intrinsic__SWAP = this.__Factory__.Get<IUnitary<(Qubit,Qubit)>>(typeof(global::Microsoft.Quantum.Intrinsic.SWAP));
        }

        public override IApplyData __DataIn__((Qubit,Qubit) data) => new In(data);
        public override IApplyData __DataOut__(QVoid data) => data;
        public static System.Threading.Tasks.Task<QVoid> Run(IOperationFactory __m__, Qubit qubitA, Qubit qubitB)
        {
            return __m__.Run<Exercise1, (Qubit,Qubit), QVoid>((qubitA, qubitB));
        }
    }

    [SourceLocation("D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs", OperationFunctor.Body, 72, 111)]
    public partial class Exercise2 : Operation<IQArray<Qubit>, QVoid>, ICallable
    {
        public Exercise2(IOperationFactory m) : base(m)
        {
        }

        String ICallable.Name => "Exercise2";
        String ICallable.FullName => "Lab2.Exercise2";
        protected ICallable Length__
        {
            get;
            set;
        }

        protected IUnitary<(Qubit,Qubit)> Microsoft__Quantum__Intrinsic__SWAP
        {
            get;
            set;
        }

        public override Func<IQArray<Qubit>, QVoid> __Body__ => (__in__) =>
        {
            var register = __in__;
#line 75 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            var len = register.Length;
#line 77 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            foreach (var i in new QRange(0L, ((len / 2L) - 1L)))
#line hidden
            {
#line 78 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
                if ((i != ((len - 1L) - i)))
                {
#line 79 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
                    Microsoft__Quantum__Intrinsic__SWAP.Apply((register[i], register[((len - 1L) - i)]));
                }
            }

#line hidden
            return QVoid.Instance;
        }

        ;
        public override void __Init__()
        {
            this.Length__ = this.__Factory__.Get<ICallable>(typeof(global::Microsoft.Quantum.Core.Length<>));
            this.Microsoft__Quantum__Intrinsic__SWAP = this.__Factory__.Get<IUnitary<(Qubit,Qubit)>>(typeof(global::Microsoft.Quantum.Intrinsic.SWAP));
        }

        public override IApplyData __DataIn__(IQArray<Qubit> data) => data;
        public override IApplyData __DataOut__(QVoid data) => data;
        public static System.Threading.Tasks.Task<QVoid> Run(IOperationFactory __m__, IQArray<Qubit> register)
        {
            return __m__.Run<Exercise2, IQArray<Qubit>, QVoid>(register);
        }
    }

    [SourceLocation("D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs", OperationFunctor.Body, 111, 155)]
    public partial class Exercise3 : Operation<IQArray<IQArray<Qubit>>, QVoid>, ICallable
    {
        public Exercise3(IOperationFactory m) : base(m)
        {
        }

        String ICallable.Name => "Exercise3";
        String ICallable.FullName => "Lab2.Exercise3";
        protected IUnitary<Qubit> Microsoft__Quantum__Intrinsic__H
        {
            get;
            set;
        }

        protected IUnitary<(Qubit,Qubit)> Microsoft__Quantum__Intrinsic__CNOT
        {
            get;
            set;
        }

        protected IUnitary<(Qubit,Qubit)> Microsoft__Quantum__Canon__CZ
        {
            get;
            set;
        }

        protected IUnitary<Qubit> Microsoft__Quantum__Intrinsic__X
        {
            get;
            set;
        }

        public override Func<IQArray<IQArray<Qubit>>, QVoid> __Body__ => (__in__) =>
        {
            var registers = __in__;
#line 116 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            foreach (var register in registers)
#line hidden
            {
#line 117 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
                Microsoft__Quantum__Intrinsic__H.Apply(register[0L]);
#line 118 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
                Microsoft__Quantum__Intrinsic__CNOT.Apply((register[0L], register[1L]));
            }

#line 123 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Canon__CZ.Apply((registers[1L][0L], registers[1L][1L]));
#line 125 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Intrinsic__X.Apply(registers[2L][1L]);
#line 127 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Canon__CZ.Apply((registers[3L][0L], registers[3L][1L]));
#line 128 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Intrinsic__X.Apply(registers[3L][1L]);
#line hidden
            return QVoid.Instance;
        }

        ;
        public override void __Init__()
        {
            this.Microsoft__Quantum__Intrinsic__H = this.__Factory__.Get<IUnitary<Qubit>>(typeof(global::Microsoft.Quantum.Intrinsic.H));
            this.Microsoft__Quantum__Intrinsic__CNOT = this.__Factory__.Get<IUnitary<(Qubit,Qubit)>>(typeof(global::Microsoft.Quantum.Intrinsic.CNOT));
            this.Microsoft__Quantum__Canon__CZ = this.__Factory__.Get<IUnitary<(Qubit,Qubit)>>(typeof(global::Microsoft.Quantum.Canon.CZ));
            this.Microsoft__Quantum__Intrinsic__X = this.__Factory__.Get<IUnitary<Qubit>>(typeof(global::Microsoft.Quantum.Intrinsic.X));
        }

        public override IApplyData __DataIn__(IQArray<IQArray<Qubit>> data) => data;
        public override IApplyData __DataOut__(QVoid data) => data;
        public static System.Threading.Tasks.Task<QVoid> Run(IOperationFactory __m__, IQArray<IQArray<Qubit>> registers)
        {
            return __m__.Run<Exercise3, IQArray<IQArray<Qubit>>, QVoid>(registers);
        }
    }

    [SourceLocation("D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs", OperationFunctor.Body, 155, 178)]
    public partial class Exercise4 : Operation<IQArray<Qubit>, QVoid>, ICallable
    {
        public Exercise4(IOperationFactory m) : base(m)
        {
        }

        String ICallable.Name => "Exercise4";
        String ICallable.FullName => "Lab2.Exercise4";
        protected IUnitary<Qubit> Microsoft__Quantum__Intrinsic__H
        {
            get;
            set;
        }

        protected ICallable Length__
        {
            get;
            set;
        }

        protected IUnitary<(Qubit,Qubit)> Microsoft__Quantum__Intrinsic__CNOT
        {
            get;
            set;
        }

        public override Func<IQArray<Qubit>, QVoid> __Body__ => (__in__) =>
        {
            var register = __in__;
#line 158 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Intrinsic__H.Apply(register[0L]);
#line 159 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            foreach (var i in new QRange(0L, (register.Length - 2L)))
#line hidden
            {
#line 160 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
                Microsoft__Quantum__Intrinsic__CNOT.Apply((register[i], register[(i + 1L)]));
            }

#line hidden
            return QVoid.Instance;
        }

        ;
        public override void __Init__()
        {
            this.Microsoft__Quantum__Intrinsic__H = this.__Factory__.Get<IUnitary<Qubit>>(typeof(global::Microsoft.Quantum.Intrinsic.H));
            this.Length__ = this.__Factory__.Get<ICallable>(typeof(global::Microsoft.Quantum.Core.Length<>));
            this.Microsoft__Quantum__Intrinsic__CNOT = this.__Factory__.Get<IUnitary<(Qubit,Qubit)>>(typeof(global::Microsoft.Quantum.Intrinsic.CNOT));
        }

        public override IApplyData __DataIn__(IQArray<Qubit> data) => data;
        public override IApplyData __DataOut__(QVoid data) => data;
        public static System.Threading.Tasks.Task<QVoid> Run(IOperationFactory __m__, IQArray<Qubit> register)
        {
            return __m__.Run<Exercise4, IQArray<Qubit>, QVoid>(register);
        }
    }

    [SourceLocation("D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs", OperationFunctor.Body, 178, -1)]
    public partial class Exercise5 : Operation<IQArray<Qubit>, QVoid>, ICallable
    {
        public Exercise5(IOperationFactory m) : base(m)
        {
        }

        String ICallable.Name => "Exercise5";
        String ICallable.FullName => "Lab2.Exercise5";
        protected IUnitary<Qubit> Microsoft__Quantum__Intrinsic__X
        {
            get;
            set;
        }

        protected IUnitary<Qubit> Microsoft__Quantum__Intrinsic__H
        {
            get;
            set;
        }

        protected IUnitary<(Qubit,Qubit)> Microsoft__Quantum__Intrinsic__CNOT
        {
            get;
            set;
        }

        protected IUnitary<(Qubit,Qubit)> Microsoft__Quantum__Canon__CZ
        {
            get;
            set;
        }

        public override Func<IQArray<Qubit>, QVoid> __Body__ => (__in__) =>
        {
            var register = __in__;
#line 181 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Intrinsic__X.Apply(register[1L]);
#line 182 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Intrinsic__H.Apply(register[2L]);
#line 183 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Intrinsic__CNOT.Apply((register[2L], register[3L]));
#line 184 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Intrinsic__X.Apply(register[3L]);
#line 185 "D:\\BWSI\\exercises\\exercises\\QSharpExercises\\Lab2\\Lab2.qs"
            Microsoft__Quantum__Canon__CZ.Apply((register[1L], register[2L]));
#line hidden
            return QVoid.Instance;
        }

        ;
        public override void __Init__()
        {
            this.Microsoft__Quantum__Intrinsic__X = this.__Factory__.Get<IUnitary<Qubit>>(typeof(global::Microsoft.Quantum.Intrinsic.X));
            this.Microsoft__Quantum__Intrinsic__H = this.__Factory__.Get<IUnitary<Qubit>>(typeof(global::Microsoft.Quantum.Intrinsic.H));
            this.Microsoft__Quantum__Intrinsic__CNOT = this.__Factory__.Get<IUnitary<(Qubit,Qubit)>>(typeof(global::Microsoft.Quantum.Intrinsic.CNOT));
            this.Microsoft__Quantum__Canon__CZ = this.__Factory__.Get<IUnitary<(Qubit,Qubit)>>(typeof(global::Microsoft.Quantum.Canon.CZ));
        }

        public override IApplyData __DataIn__(IQArray<Qubit> data) => data;
        public override IApplyData __DataOut__(QVoid data) => data;
        public static System.Threading.Tasks.Task<QVoid> Run(IOperationFactory __m__, IQArray<Qubit> register)
        {
            return __m__.Run<Exercise5, IQArray<Qubit>, QVoid>(register);
        }
    }
}
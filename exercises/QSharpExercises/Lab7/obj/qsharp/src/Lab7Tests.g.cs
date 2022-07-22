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

[assembly: CallableDeclaration("{\"Kind\":{\"Case\":\"Operation\"},\"QualifiedName\":{\"Namespace\":\"QSharpExercises.Tests.Lab7\",\"Name\":\"Exercise1Test\"},\"Attributes\":[{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Diagnostics\",\"Name\":\"Test\",\"Range\":{\"Case\":\"Value\",\"Fields\":[{\"Item1\":{\"Line\":1,\"Column\":2},\"Item2\":{\"Line\":1,\"Column\":6}}]}}]},\"TypeIdRange\":{\"Case\":\"Value\",\"Fields\":[{\"Item1\":{\"Line\":1,\"Column\":2},\"Item2\":{\"Line\":1,\"Column\":6}}]},\"Argument\":{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"QuantumSimulator\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Value\",\"Fields\":[{\"Item1\":{\"Line\":1,\"Column\":7},\"Item2\":{\"Line\":1,\"Column\":25}}]}},\"Offset\":{\"Item1\":14,\"Item2\":4},\"Comments\":{\"OpeningComments\":[\" open QSharpExercises.Solutions.Lab7;\"],\"ClosingComments\":[]}},{\"TypeId\":{\"Case\":\"Value\",\"Fields\":[{\"Namespace\":\"Microsoft.Quantum.Targeting\",\"Name\":\"RequiresCapability\",\"Range\":{\"Case\":\"Null\"}}]},\"TypeIdRange\":{\"Case\":\"Null\"},\"Argument\":{\"Item1\":{\"Case\":\"ValueTuple\",\"Fields\":[[{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Transparent\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Full\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},{\"Item1\":{\"Case\":\"StringLiteral\",\"Fields\":[\"Inferred automatically by the compiler.\",[]]},\"Item2\":[],\"Item3\":{\"Case\":\"String\"},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}}]]},\"Item2\":[],\"Item3\":{\"Case\":\"TupleType\",\"Fields\":[[{\"Case\":\"String\"},{\"Case\":\"String\"},{\"Case\":\"String\"}]]},\"Item4\":{\"IsMutable\":false,\"HasLocalQuantumDependency\":false},\"Item5\":{\"Case\":\"Null\"}},\"Offset\":{\"Item1\":0,\"Item2\":0},\"Comments\":{\"OpeningComments\":[],\"ClosingComments\":[]}}],\"Modifiers\":{\"Access\":{\"Case\":\"DefaultAccess\"}},\"SourceFile\":\"D:\\\\BWSI\\\\Exercises\\\\exercises\\\\QSharpExercises\\\\Lab7\\\\Lab7Tests\\\\Lab7Tests.qs\",\"Position\":{\"Item1\":15,\"Item2\":4},\"SymbolRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":24}},\"ArgumentTuple\":{\"Case\":\"QsTuple\",\"Fields\":[[]]},\"Signature\":{\"TypeParameters\":[],\"ArgumentType\":{\"Case\":\"UnitType\"},\"ReturnType\":{\"Case\":\"UnitType\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}}},\"Documentation\":[]}")]
[assembly: SpecializationDeclaration("{\"Kind\":{\"Case\":\"QsBody\"},\"TypeArguments\":{\"Case\":\"Null\"},\"Information\":{\"Characteristics\":{\"Case\":\"EmptySet\"},\"InferredInformation\":{\"IsSelfAdjoint\":false,\"IsIntrinsic\":false}},\"Parent\":{\"Namespace\":\"QSharpExercises.Tests.Lab7\",\"Name\":\"Exercise1Test\"},\"Attributes\":[],\"SourceFile\":\"D:\\\\BWSI\\\\Exercises\\\\exercises\\\\QSharpExercises\\\\Lab7\\\\Lab7Tests\\\\Lab7Tests.qs\",\"Position\":{\"Item1\":15,\"Item2\":4},\"HeaderRange\":{\"Item1\":{\"Line\":1,\"Column\":11},\"Item2\":{\"Line\":1,\"Column\":24}},\"Documentation\":[]}")]
#line hidden
namespace QSharpExercises.Tests.Lab7
{
    [SourceLocation("D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs", OperationFunctor.Body, 16, -1)]
    public partial class Exercise1Test : Operation<QVoid, QVoid>, ICallable
    {
        public Exercise1Test(IOperationFactory m) : base(m)
        {
        }

        public class QuantumSimulator
        {
            public QuantumSimulator(Xunit.Abstractions.ITestOutputHelper Output)
            {
                this.Output = Output;
            }

            internal Xunit.Abstractions.ITestOutputHelper Output
            {
                get;
            }

            [Xunit.Fact()]
            [Xunit.Trait("Target", "QuantumSimulator")]
            [Xunit.Trait("Name", "Exercise1Test")]
            public void Exercise1Test()
#line 16 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
            {
                var sim = new Microsoft.Quantum.Simulation.Simulators.QuantumSimulator();
                if (sim is Microsoft.Quantum.Simulation.Common.SimulatorBase baseSim && this.Output != null)
                {
                    baseSim.OnLog += this.Output.WriteLine;
                }

                try
                {
                    sim.Execute<Exercise1Test, QVoid, QVoid>(QVoid.Instance);
                }
                catch
                {
#line 16 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
                    Xunit.Assert.True(false, "Q# Test failed. For details see the Standard output below.");
                }
                finally
                {
                    if (sim is IDisposable disposeSim)
                    {
                        disposeSim.Dispose();
                    }
                }
            }
        }

        String ICallable.Name => "Exercise1Test";
        String ICallable.FullName => "QSharpExercises.Tests.Lab7.Exercise1Test";
        protected ICallable<Double, Boolean> Microsoft__Quantum__Random__DrawRandomBool
        {
            get;
            set;
        }

        protected ICallable<(ICallable,IQArray<Boolean>), IQArray<Boolean>> Lab7__Exercise1
        {
            get;
            set;
        }

        protected ICallable<(IQArray<Qubit>,IQArray<Qubit>), QVoid> Lab7__Copy
        {
            get;
            set;
        }

        protected ICallable<(IQArray<Boolean>,IQArray<Boolean>,String), QVoid> Microsoft__Quantum__Diagnostics__AllEqualityFactB
        {
            get;
            set;
        }

        protected ICallable<(IQArray<Qubit>,IQArray<Qubit>), QVoid> Lab7__LeftShiftBy1
        {
            get;
            set;
        }

        protected ICallable Length__
        {
            get;
            set;
        }

        public override Func<QVoid, QVoid> __Body__ => (__in__) =>
        {
#line 17 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
            foreach (var numQubits in new QRange(3L, 10L))
#line hidden
            {
#line 18 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
                var randomInput = QArray<Boolean>.Create(0L);
#line 19 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
                foreach (var i in new QRange(1L, numQubits))
#line hidden
                {
#line 20 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
                    randomInput = QArray<Boolean>.Add(randomInput, new QArray<Boolean>(Microsoft__Quantum__Random__DrawRandomBool.Apply(0.5D)));
                }

#line 23 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
                var copyOutput = (IQArray<Boolean>)Lab7__Exercise1.Apply((Lab7__Copy, randomInput?.Copy()));
#line 24 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
                Microsoft__Quantum__Diagnostics__AllEqualityFactB.Apply((copyOutput, randomInput?.Copy(), "Incorrect output for Copy operation"));
#line 30 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
                var shiftOutput = (IQArray<Boolean>)Lab7__Exercise1.Apply((Lab7__LeftShiftBy1, randomInput?.Copy()));
#line 31 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
                var expected = (IQArray<Boolean>)QArray<Boolean>.Add(randomInput.Slice(new QRange(1L, (randomInput.Length - 1L))), new QArray<Boolean>(false));
#line 32 "D:\\BWSI\\Exercises\\exercises\\QSharpExercises\\Lab7\\Lab7Tests\\Lab7Tests.qs"
                Microsoft__Quantum__Diagnostics__AllEqualityFactB.Apply((shiftOutput, expected, "Incorrect output for LeftShiftBy1 operation"));
            }

#line hidden
            return QVoid.Instance;
        }

        ;
        public override void __Init__()
        {
            this.Microsoft__Quantum__Random__DrawRandomBool = this.__Factory__.Get<ICallable<Double, Boolean>>(typeof(global::Microsoft.Quantum.Random.DrawRandomBool));
            this.Lab7__Exercise1 = this.__Factory__.Get<ICallable<(ICallable,IQArray<Boolean>), IQArray<Boolean>>>(typeof(global::Lab7.Exercise1));
            this.Lab7__Copy = this.__Factory__.Get<ICallable<(IQArray<Qubit>,IQArray<Qubit>), QVoid>>(typeof(global::Lab7.Copy));
            this.Microsoft__Quantum__Diagnostics__AllEqualityFactB = this.__Factory__.Get<ICallable<(IQArray<Boolean>,IQArray<Boolean>,String), QVoid>>(typeof(global::Microsoft.Quantum.Diagnostics.AllEqualityFactB));
            this.Lab7__LeftShiftBy1 = this.__Factory__.Get<ICallable<(IQArray<Qubit>,IQArray<Qubit>), QVoid>>(typeof(global::Lab7.LeftShiftBy1));
            this.Length__ = this.__Factory__.Get<ICallable>(typeof(global::Microsoft.Quantum.Core.Length<>));
        }

        public override IApplyData __DataIn__(QVoid data) => data;
        public override IApplyData __DataOut__(QVoid data) => data;
        public static System.Threading.Tasks.Task<QVoid> Run(IOperationFactory __m__)
        {
            return __m__.Run<Exercise1Test, QVoid, QVoid>(QVoid.Instance);
        }
    }
}
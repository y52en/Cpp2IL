using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using AsmTypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using AsmMethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class IntegralOperandWidthTests
{
    [TestCase(OpCode.Add, false)]
    [TestCase(OpCode.Subtract, false)]
    [TestCase(OpCode.Multiply, false)]
    [TestCase(OpCode.Divide, false)]
    [TestCase(OpCode.Modulo, false)]
    [TestCase(OpCode.Add, true)]
    [TestCase(OpCode.Subtract, true)]
    [TestCase(OpCode.Multiply, true)]
    [TestCase(OpCode.Divide, true)]
    [TestCase(OpCode.Modulo, true)]
    [TestCase(OpCode.CheckLess, true)]
    [TestCase(OpCode.CheckGreater, true)]
    [TestCase(OpCode.CheckLessOrEqual, true)]
    [TestCase(OpCode.CheckGreaterOrEqual, true)]
    public void ActualEmittedIlUsesMatchingIntegralLiteralWidthAndExecutes(OpCode opcode, bool wide)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var comparison = opcode is OpCode.CheckLess or OpCode.CheckGreater or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual;
        var scalar = wide ? app.SystemTypes.SystemInt64Type : app.SystemTypes.SystemInt32Type;
        var returnType = comparison ? app.SystemTypes.SystemBooleanType : scalar;
        var input = new LocalVariable("input", new Register(null, "X0"), scalar);
        var result = new LocalVariable("result", new Register(null, "X1"), returnType);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Compute", returnType, MethodAttributes.Public | MethodAttributes.Static, [scalar]);
        context.ParameterLocals = [input]; context.Locals = [input, result]; context.AnalysisWarnings = [];
        foreach (var constantFirst in new[] { false, true })
        {
            var assembly = new AssemblyDefinition("Integral" + Guid.NewGuid().ToString("N"), new Version(1, 0));
            var module = new ModuleDefinition("Integral.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0))); assembly.Modules.Add(module);
            var type = new TypeDefinition("Test", "Generated", AsmTypeAttributes.Public, module.CorLibTypeFactory.Object.Type); module.TopLevelTypes.Add(type);
            var parameterType = wide ? module.CorLibTypeFactory.Int64 : module.CorLibTypeFactory.Int32;
            var outputType = comparison ? module.CorLibTypeFactory.Boolean : parameterType;
            var method = new MethodDefinition("Compute", AsmMethodAttributes.Public | AsmMethodAttributes.Static, MethodSignature.CreateStatic(outputType, [parameterType])); type.Methods.Add(method);
            method.ParameterDefinitions.Add(new ParameterDefinition(1, "input", 0));
            method.CilMethodBody = new CilMethodBody { InitializeLocals = true };
            var resultLocal = new CilLocalVariable(outputType); method.CilMethodBody.LocalVariables.Add(resultLocal);
            var locals = new Dictionary<LocalVariable, CilLocalVariable> { { result, resultLocal } };
            var instruction = constantFirst ? new Instruction(0, opcode, result, new Immediate(3), input) : new Instruction(0, opcode, result, input, new Immediate(3));
            var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
            emit.Invoke(null, [instruction, context, method, locals, method]);
            emit.Invoke(null, [new Instruction(1, OpCode.Return, result), context, method, locals, method]);
            Assert.That(method.CilMethodBody.Instructions.Any(i => i.OpCode == (wide ? CilOpCodes.Ldc_I8 : CilOpCodes.Ldc_I4) && Convert.ToInt64(i.Operand) == 3), Is.True, "literal must have the evaluation-stack width of the proven integral operand");
            using var stream = new MemoryStream(); module.Write(stream);
            var generated = System.Reflection.Assembly.Load(stream.ToArray()).GetType("Test.Generated")!.GetMethod("Compute")!;
            foreach (var value in new[] { -9L, -1L, 1L, 3L, 9L, long.MinValue + 5, long.MaxValue - 5 })
            {
                var x = wide ? value : unchecked((int)value);
                var a = constantFirst ? 3 : x; var b = constantFirst ? x : 3;
                object expected;
                if (comparison)
                    expected = opcode switch { OpCode.CheckLess => a < b, OpCode.CheckGreater => a > b, OpCode.CheckLessOrEqual => a <= b, _ => a >= b };
                else
                {
                    var number = opcode switch { OpCode.Add => unchecked(a + b), OpCode.Subtract => unchecked(a - b), OpCode.Multiply => unchecked(a * b), OpCode.Divide => a / b, _ => a % b };
                    expected = wide ? (object)number : unchecked((int)number);
                }
                object argument = wide ? (object)x : unchecked((int)x);
                Assert.That(generated.Invoke(null, [argument]), Is.EqualTo(expected), $"{opcode}: {a},{b}");
            }
        }
    }
}

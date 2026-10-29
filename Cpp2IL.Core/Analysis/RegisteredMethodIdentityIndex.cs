using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Native registrations are stable after ApplicationAnalysisContext construction.
// Buckets use definition object identity; every returned row still has to belong
// to the current registry under its own MethodRef before it can authorize a call.
internal static class RegisteredMethodIdentityIndex
{
    private sealed class Index
    {
        private int count=-1;
        private Dictionary<MethodAnalysisContext,ConcreteGenericMethodAnalysisContext[]> groups=new(ReferenceEqualityComparer.Instance);
        internal ConcreteGenericMethodAnalysisContext[] Get(ApplicationAnalysisContext app,MethodAnalysisContext definition)
        {
            lock(this)
            {
                var table=app.ConcreteGenericMethodsByRef;
                bool Live(ConcreteGenericMethodAnalysisContext method)=>method.MethodRef!=null
                    && ReferenceEquals(method.AppContext,app)
                    && table.TryGetValue(method.MethodRef,out var registered)&&ReferenceEquals(registered,method);
                if(count!=table.Count || groups.TryGetValue(definition,out var old)&&old.Any(row=>!Live(row)))
                {
                    var collected=new Dictionary<MethodAnalysisContext,List<ConcreteGenericMethodAnalysisContext>>(ReferenceEqualityComparer.Instance);
                    foreach(var row in table.Values.Where(Live))
                    {
                        if(!collected.TryGetValue(row.BaseMethodContext,out var bucket))
                            collected[row.BaseMethodContext]=bucket=[];
                        bucket.Add(row);
                    }
                    groups=new(ReferenceEqualityComparer.Instance);
                    foreach(var pair in collected)groups.Add(pair.Key,pair.Value.ToArray());
                    count=table.Count;
                }
                return groups.TryGetValue(definition,out var rows)?rows.Where(Live).ToArray():[];
            }
        }
    }
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Index> Indices=new();
    internal static IReadOnlyList<ConcreteGenericMethodAnalysisContext> Candidates(MethodAnalysisContext method)
    {
        var definition=method is ConcreteGenericMethodAnalysisContext concrete?concrete.BaseMethodContext:method;
        return Indices.GetValue(method.AppContext,_=>new Index()).Get(method.AppContext,definition);
    }
}

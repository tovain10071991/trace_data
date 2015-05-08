// $ ~/Documents/test/trace_syscall$ /home/user/Documents/pin-2.14-71313-gcc.4.4.7-linux/pin -t obj-ia32/trace_syscall.so -- ../syscall_test/a.out

#include <syscall.h>
#include "pin.H"
#include <fstream>
#include <list>
#include <iostream>
#include <cstring>
#include <stdlib.h>
#include <vector>
#include <map>
#include <map>
#include <set>
#include <stdio.h>

using namespace std;

ofstream fout;
ofstream fins_dis;
ofstream fins_dis_det;
ofstream ftrace_taint;
ofstream ftrace_analysis;
ofstream fins_analysis;

UINT32 count1=0;
UINT32 count2=0;
UINT32 count3=0;
UINT32 count4=0;

map<ADDRINT, pair<vector<ADDRINT>, vector<ADDRINT> > > ins_reg;
//ins_reg[key].first为read_reg, ins_reg[key].second为write_reg

ADDRINT start_addr;
ADDRINT main_addr;
ADDRINT exit_addr;

BOOL start_flag = false;
BOOL main_flag = false;

map<ADDRINT, ADDRINT>	taint_mem;
vector<BOOL>	taint_reg(REG_LAST, false);
/*
VOID print_tatus()
{
	f << "STATUS" << endl;
	for(map<ADDRINT, ADDRINT>::iterator iter=taint_mem.begin();iter!=taint_mem.end();++iter)
		fout << (*iter).first << " ~ " << (*iter).second << "\t";
	fout << endl;
	for(UINT32 i=0;i<REG_LAST;i++)
		if(taint_reg[i])
			fout << i << "\t";
	fout << endl;
}
*/
VOID add_taint_mem(ADDRINT min, ADDRINT max)
{
	fins_analysis << "add mem: 0x" << min << " ~ 0x" << max << endl;
	map<ADDRINT, ADDRINT>::iterator iter=taint_mem.lower_bound(min);
	map<ADDRINT, ADDRINT>::iterator pre_iter=iter;
	pre_iter--;
	map<ADDRINT, ADDRINT>::iterator work_iter=pre_iter;
	vector<map<ADDRINT, ADDRINT>::iterator> del_iters;

	if((*pre_iter).second+1>=min)
	{
		//与前重叠或连接
		(*pre_iter).second=max>(*pre_iter).second?max:(*pre_iter).second;
	}
	else
	{
		//与前不连接
		taint_mem[min]=max;
		work_iter=taint_mem.find(min);
	}
	//将后项与该项重叠或连接的项都合并
	for(;iter!=taint_mem.end()&&(*iter).first-1<=max;++iter)
	{
		(*work_iter).second=max>(*iter).second?max:(*iter).second;
		del_iters.push_back(iter);
	}
	for(vector<map<ADDRINT, ADDRINT>::iterator>::iterator del_iter=del_iters.begin();del_iter!=del_iters.end();++del_iter)
		taint_mem.erase((*del_iter));
}


VOID del_taint_mem(ADDRINT min, ADDRINT max)
{
	fins_analysis << "remove mem: 0x" << min << " ~ 0x" << max << endl;
	map<ADDRINT, ADDRINT>::iterator iter=taint_mem.lower_bound(min);
	map<ADDRINT, ADDRINT>::iterator pre_iter=iter;
	pre_iter--;
	vector<map<ADDRINT, ADDRINT>::iterator> del_iters;

	if(max<(*pre_iter).second)
	{
		//被前包含
		taint_mem[max]=(*pre_iter).second;
		(*pre_iter).second=min;
	}
	else
	{
		//将前项的尾部切掉
		(*pre_iter).second=min<(*pre_iter).second?min:(*pre_iter).second;
		//将后项的被包含项和最后重叠项的头部切掉
		for(;iter!=taint_mem.end()&&(*iter).first<=max;++iter)
		{
			if((*iter).second>max)
			{
				taint_mem[max]=(*iter).second;
			}
			del_iters.push_back(iter);
		}
		for(vector<map<ADDRINT, ADDRINT>::iterator>::iterator del_iter=del_iters.begin();del_iter!=del_iters.end();++del_iter)
			taint_mem.erase((*del_iter));
	}
}

VOID ins_start(ADDRINT ins_addr, CONTEXT* ctxt)
{
	if(ins_addr!=start_addr)
		return;
	//从esp往上依次是argc，argv[0]，argv[1]，...，0，所以先读取esp
	ADDRINT esp = PIN_GetContextReg(ctxt, REG_ESP);
	UINT32 argc = *(UINT32*)(esp);
	char* argv[argc];
	for(UINT32 i=0;i<argc;i++)
	{
		argv[i] = *(char**)(esp+4+4*i);
		cout << esp+4+4*i << "\t" << (UINT32)argv[i] << "\t" << argv[i] << endl;
		//所指内存标记为污点
		add_taint_mem((ADDRINT)argv[i], (ADDRINT)argv[i]+strlen(argv[i]));
	}
}

VOID ins_exit(ADDRINT ins_addr)
{
	if(ins_addr!=exit_addr)
		return;
	PIN_RemoveInstrumentation();
	PIN_Detach(); 
}

VOID ins_read_write(ADDRINT ins_addr, ADDRINT read_addr, UINT32 read_size, ADDRINT write_addr, UINT32 write_size)
{
	fins_analysis << "read&write: 0x" << ins_addr << endl;
	map<ADDRINT, ADDRINT>::iterator iter=taint_mem.lower_bound(read_addr);
	map<ADDRINT, ADDRINT>::iterator pre_iter=iter;
	pre_iter--;
	//只要读的寄存器或内存有一个是污点，写的寄存器和内存全部标记为污点
	//先看看读的寄存器中有没有污点
	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].first.begin();iter!=ins_reg[ins_addr].first.end();++iter)
	{
		if(taint_reg[(*iter)])
			goto set_taint;
	}
	//再判断被读内存中有没有污点单元
	if(!((*pre_iter).second<read_addr&&(*iter).first>read_addr+read_size))
		goto set_taint;
	//没有污点读，就把被写的都标记为非污点
	fins_analysis << "remove taint reg: " << "\t";
	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].second.begin();iter!=ins_reg[ins_addr].second.end();++iter)
	{
		fins_analysis << (*iter) << "\t";
		taint_reg[(*iter)]=false;
	}
	fins_analysis << endl;
	cout << "0x" << ins_addr << "\tremove mem: 0x" << write_addr << " ~ 0x" << write_addr+write_size << endl;
	del_taint_mem(write_addr, write_addr+write_size);
	ins_reg.erase(ins_addr);
	fins_analysis << endl;
	return;
set_taint:
	fins_analysis << "add taint reg: " << "\t";	

	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].second.begin();iter!=ins_reg[ins_addr].second.end();++iter)
	{
		fins_analysis << (*iter) << "\t";
		taint_reg[(*iter)]=true;
	}
	fins_analysis << endl;
	cout << "0x" << ins_addr << "\tadd mem: 0x" << write_addr << " ~ 0x" << write_addr+write_size << endl;
	add_taint_mem(write_addr, write_addr+write_size);
	ins_reg.erase(ins_addr);
	fins_analysis << endl;
	return;
}

VOID ins_read(ADDRINT ins_addr, ADDRINT read_addr, UINT32 read_size)
{
	fins_analysis << "read: 0x" << ins_addr << endl;
	map<ADDRINT, ADDRINT>::iterator iter=taint_mem.lower_bound(read_addr);
	map<ADDRINT, ADDRINT>::iterator pre_iter=iter;
	pre_iter--;
	//只要读的寄存器或内存有一个是污点，写的寄存器全部标记为污点
	//先看看读的寄存器中有没有污点
	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].first.begin();iter!=ins_reg[ins_addr].first.end();++iter)
	{
		if(taint_reg[(*iter)])
			goto set_taint;
	}
	//再判断被读内存中有没有污点单元
	if(!((*pre_iter).second<read_addr&&(*iter).first>read_addr+read_size))
		goto set_taint;
	//没有污点读，就把被写的都标记为非污点
	fins_analysis << "remove taint reg: " << "\t";
	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].second.begin();iter!=ins_reg[ins_addr].second.end();++iter)
	{
		fins_analysis << (*iter) << "\t";
		taint_reg[(*iter)]=false;
	}
	fins_analysis << endl;
	ins_reg.erase(ins_addr);
	return;
set_taint:
	fins_analysis << "add taint reg: " << "\t";	

	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].second.begin();iter!=ins_reg[ins_addr].second.end();++iter)
	{
		fins_analysis << (*iter) << "\t";
		taint_reg[(*iter)]=true;
	}
	fins_analysis << endl;
	ins_reg.erase(ins_addr);
	return;
}

VOID ins_write(ADDRINT ins_addr, ADDRINT write_addr, UINT32 write_size)
{
	fins_analysis << "write: 0x" << ins_addr << endl;
	//只要读的寄存器有一个是污点，写的寄存器和内存全部标记为污点
	//先看看读的寄存器中有没有污点
	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].first.begin();iter!=ins_reg[ins_addr].first.end();++iter)
	{
		if(taint_reg[(*iter)])
			goto set_taint;
	}
	//没有污点读，就把被写的都标记为非污点
	fins_analysis << "remove taint reg: " << "\t";
	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].second.begin();iter!=ins_reg[ins_addr].second.end();++iter)
	{
		fins_analysis << (*iter) << "\t";
		taint_reg[(*iter)]=false;
	}
	fins_analysis << endl;
	cout << "0x" << ins_addr << "\tremove mem: 0x" << write_addr << " ~ 0x" << write_addr+write_size << endl;
	del_taint_mem(write_addr, write_addr+write_size);
	ins_reg.erase(ins_addr);
	fins_analysis << endl;
	return;
set_taint:
	fins_analysis << "add taint reg: " << "\t";	

	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].second.begin();iter!=ins_reg[ins_addr].second.end();++iter)
	{
		fins_analysis << (*iter) << "\t";
		taint_reg[(*iter)]=true;
	}
	fins_analysis << endl;
	cout << "0x" << ins_addr << "\tadd mem: 0x" << write_addr << " ~ 0x" << write_addr+write_size << endl;
	add_taint_mem(write_addr, write_addr+write_size);
	ins_reg.erase(ins_addr);
	fins_analysis << endl;
	return;
}

VOID ins_none(ADDRINT ins_addr)
{
	fins_analysis << "none: 0x" << ins_addr << endl;
	//只要读的寄存器有一个是污点，写的寄存器全部标记为污点
	//先看看读的寄存器中有没有污点
	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].first.begin();iter!=ins_reg[ins_addr].first.end();++iter)
	{
		if(taint_reg[(*iter)])
			goto set_taint;
	}
	//没有污点读，就把被写的都标记为非污点
	fins_analysis << "remove taint reg: " << "\t";
	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].second.begin();iter!=ins_reg[ins_addr].second.end();++iter)
	{
		fins_analysis << (*iter) << "\t";
		taint_reg[(*iter)]=false;
	}
	fins_analysis << endl;
	ins_reg.erase(ins_addr);
	fins_analysis << endl;
	return;
set_taint:
	fins_analysis << "add taint reg: " << "\t";	

	for(vector<ADDRINT>::iterator iter=ins_reg[ins_addr].second.begin();iter!=ins_reg[ins_addr].second.end();++iter)
	{
		fins_analysis << (*iter) << "\t";
		taint_reg[(*iter)]=true;
	}
	fins_analysis << endl;
	ins_reg.erase(ins_addr);
	fins_analysis << endl;
	return;
}

void ins_instrument(INS ins, VOID* v)
{
	if(start_flag==false)
	{
		if(start_addr!=INS_Address(ins))
			return;
		else
		{
			// 先把被测程序的参数标记为污点
			INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_start, IARG_INST_PTR, IARG_CONST_CONTEXT, IARG_END);
			start_flag = true;
		}
	}
	if(main_flag==false)
	{
		if(main_addr!=INS_Address(ins))
			return;
		else
		{
			main_flag = true;
		}
	}
	if(INS_Address(ins)==exit_addr)
	{
		// 退出时除去所有插桩
		INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_exit, IARG_INST_PTR, IARG_END);
	}
	fins_dis << "0x" << INS_Address(ins) << "\t" << INS_Disassemble(ins) << endl;
	fout << INS_Disassemble(ins) << endl;
	fins_dis_det << "0x" << INS_Address(ins) << "\t" << INS_Disassemble(ins) << endl;

	pair<vector<ADDRINT>, vector<ADDRINT> > rw_reg;
	vector<ADDRINT> read_reg;
	vector<ADDRINT> write_reg;

	for(UINT32 i=0;INS_RegR(ins, i);i++)
	{
		read_reg.push_back(INS_RegR(ins, i));
	}
	for(UINT32 i=0;INS_RegW(ins, i);i++)
	{
		write_reg.push_back(INS_RegW(ins, i));
	}

	rw_reg.first = read_reg;
	rw_reg.second = write_reg;
	ins_reg[INS_Address(ins)] = rw_reg;

	if(INS_IsMemoryRead(ins)&&INS_IsMemoryWrite(ins))
	{
		fins_dis_det << "Read&Write" << endl;
		INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_read_write, IARG_INST_PTR, IARG_MEMORYREAD_EA, IARG_MEMORYREAD_SIZE, IARG_MEMORYWRITE_EA, IARG_MEMORYWRITE_SIZE, IARG_END);
	}
	else if(INS_IsMemoryRead(ins))
	{
		fins_dis_det << "Read" << endl;
		INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_read, IARG_INST_PTR, IARG_MEMORYREAD_EA, IARG_MEMORYREAD_SIZE, IARG_END);
	}
	else if(INS_IsMemoryWrite(ins))
	{
		fins_dis_det << "Write" << endl;
		INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_write, IARG_INST_PTR, IARG_MEMORYWRITE_EA, IARG_MEMORYWRITE_SIZE, IARG_END);
	}
	else
	{
		fins_dis_det << "None" << endl;
		INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_none, IARG_INST_PTR, IARG_END);
	}
	fins_dis_det << "Read regs" << "\t";
	for(vector<ADDRINT>::iterator iter=rw_reg.first.begin();iter!=rw_reg.first.end();++iter)
		fins_dis_det << (*iter) << "\t";
	fins_dis_det << endl;
	fins_dis_det << "Write regs" << "\t";
	for(vector<ADDRINT>::iterator iter=rw_reg.second.begin();iter!=rw_reg.second.end();++iter)
		fins_dis_det << (*iter) << "\t";
	fins_dis_det << endl << endl;
}

VOID trace_instrument(TRACE trace, VOID* v)
{
	if(main_flag==false)
		return;
	ftrace_taint << "0x" << TRACE_Address(trace) << endl;
	for(map<ADDRINT,ADDRINT>::iterator iter = taint_mem.begin();iter!=taint_mem.end();++iter)
		ftrace_taint << "0x" << (*iter).first << " ~ 0x" << (*iter).second << "\t";
	ftrace_taint << endl;
	for(UINT32 i=0;i<REG_LAST;i++)
		if(taint_reg[i])
			ftrace_taint << i << "\t";
	ftrace_taint << endl << endl;
}

VOID img_instrument(IMG img, VOID* v)
{
	if(IMG_Type(img)!=IMG_TYPE_SHARED)
		return;
	cout << "主执行模块: " << IMG_Name(img) << endl;
	RTN rtn=RTN_FindByName(img, "main");
	if(rtn==RTN_Invalid())
	{
		cerr << "Error: main not found" << endl;
		exit(-1);
	}
	main_addr = RTN_Address(rtn);
	cout << "main's entry: 0x" << hex << main_addr << endl;
	RTN_Open(rtn);
	INS exit_ins=RTN_InsTail(rtn);
	if(exit_ins==INS_Invalid())
	{
		cerr << "Error: invalid exit ins" << endl;
		exit(-1);
	}
	exit_addr = INS_Address(exit_ins);
	cout << "main's exit: 0x" << exit_addr << endl;
	RTN_Close(rtn);
	rtn=RTN_FindByName(img, "_start");
	if(rtn==RTN_Invalid())
	{
		cerr << "Error: _start not found" << endl;
		exit(-1);
	}
	start_addr = RTN_Address(rtn);
	cout << "_start's entry: 0x" << hex << start_addr << endl;
}

int main(int argc, char *argv[])
{
	fout.open("out");
    fins_dis.open("ins.dis");
	fins_dis_det.open("ins.dis.detail");
	ftrace_taint.open("trace.taint");
	ftrace_analysis.open("trace.analysis");
	fins_analysis.open("ins.analysis");
	fout << hex;
	fins_dis << hex;
	fins_dis_det << hex;
	ftrace_taint << hex;
	ftrace_analysis << hex;
	fins_analysis << hex;

	PIN_InitSymbols();
    PIN_Init(argc, argv);

	taint_mem[0xffffffff]=0xffffffff;
	taint_mem[0]=0;

	IMG_AddInstrumentFunction(img_instrument, 0);	//为了找到主执行模块，从中找到main的入口地址
	INS_AddInstrumentFunction(ins_instrument, 0);	//判断指令类型并分别插入分析函数
	TRACE_AddInstrumentFunction(trace_instrument, 0);	//输出污点信息

    PIN_StartProgram();
    
    return 0;
}

// -fno-operator-names

#include <algorithm>
#include <array>
#include <deque>
#include <functional>
#include <iostream>
#include <iterator>
#include <numeric>
#include <set>
#include <unordered_set>
#include <vector>


enum address_mode_t
{
    reg,    // add rd,rs,rr
    imm     // add rd,rs,#i
};

typedef std::uint8_t byte_t;
typedef std::uint32_t word_t;
const unsigned word_size(sizeof(word_t));

const unsigned register_null(-1);
const unsigned
    n_registers(16),
    lr(n_registers - 2),
    n_fetch(8),
    n_speculative_levels(2),
    n_pipeline(5);


template<class OutputIt, class Size, class T>
OutputIt iota_n(OutputIt first, Size count, T value)
{
    for (Size i(count); i > 0; --i)
    {
        *first++ = value;
        ++value;
    }
    return first;
}


class Processor;

class Instruction
{
protected:
    Processor* processor;

public:
    unsigned rd = -1, rs = -1, rr = -1;
    word_t vs, vr;
    unsigned rrd = -1, rrs= -1, rrr = -1;
    unsigned speculativeLevel;

    virtual void execute() const {}

    virtual void fetch() {} // Actually predecode. Also stores PC for branches

    void setProcessor(Processor& processor_in)
    {
        processor = &processor_in;
    }
};
typedef std::vector<Instruction*> program_t;
const Instruction null;


class Program : public std::vector<Instruction*>
{
    typedef std::vector<Instruction*> parent;

public:
    Program() = default;

    Program(std::initializer_list<Instruction*> instructions, Processor& processor)
        : parent(instructions)
    {
        for (Instruction* i : *this)
            i->setProcessor(processor);;
    }
};


struct RegisterFile_entry
{
    word_t value;
    bool reserved{false};
    unsigned i_registerStatusTable;
};

class RegisterFile
{
public:
    std::array<RegisterFile_entry, n_registers> entries[n_speculative_levels];

    void speculation_confirm()
    {
        for (unsigned i(1); i < n_speculative_levels; ++i)
            entries[i - 1] = entries[i];
    }

    void speculation_deny()
    {
        for (unsigned i(1); i < n_speculative_levels; ++i)
            entries[i] = entries[0];
    }
};


class RegisterStatusTable
{
    static const unsigned n_rename_registers{n_registers};

public:
    struct Entry
    {
        word_t value;
        unsigned speculativeLevel;
        bool valid; // Implies busy (but not vice versa)
    };

private:
    std::unordered_set<unsigned>
        busy,
        busy_not;

public:
    std::array<Entry, n_rename_registers> entries;

    RegisterStatusTable()
    {
        busy.reserve(n_rename_registers);
        busy_not.reserve(n_rename_registers);
        iota_n(std::inserter(busy_not, std::begin(busy_not)), n_rename_registers, 0);
    }

    bool full()
    {
        return busy.size() == n_rename_registers;
    }

    bool isBusy(unsigned i_entry)
    {
        return busy.count(i_entry) != 0;
    }

    void setBusy(unsigned i_entry)
    {
        busy_not.erase(i_entry);
        busy.insert(i_entry);
    }

    void clearBusy(unsigned i_entry)
    {
        busy.erase(i_entry);
        busy_not.insert(i_entry);
    }

    void speculation_confirm()
    {
        for (Entry& entry : entries)
            if (entry.speculativeLevel != 0)
                --entry.speculativeLevel;
    }

    void speculation_deny()
    {
        for (unsigned i(0); i < n_rename_registers; ++i)
            if (entries[i].speculativeLevel != 0)
                clearBusy(i);
    }

    void processDispatchSourceRegister(unsigned r, word_t& v, unsigned& rr, unsigned speculativeLevel, RegisterFile& registerFile)
    {
        if (r == register_null)
            return;

        RegisterFile_entry& registerFileEntry(registerFile.entries[speculativeLevel][r]);
        if (!registerFileEntry.reserved)
            v = registerFileEntry.value;
        else
        {
            Entry& entry(entries[registerFileEntry.i_registerStatusTable]);
            if (entry.valid)
                v = entry.value;
            else
                rr = registerFileEntry.i_registerStatusTable;
        }
    }

    void processDispatchDestinationRegister(unsigned rd, unsigned& rrd, unsigned speculativeLevel, RegisterFile& registerFile)
    {
        if (rd == register_null)
            return;

        RegisterFile_entry& registerFileEntry(registerFile.entries[speculativeLevel][rd]);
        rrd = *busy_not.begin();
        setBusy(rrd);
        entries[rrd].valid = false;
        entries[rrd].speculativeLevel = speculativeLevel;
        registerFileEntry.i_registerStatusTable = rrd;
        registerFileEntry.reserved = true;
    }

    void processIssueSourceRegister(word_t& v, unsigned& rr)
    {
        if (rr == register_null)
            return;

        if (entries[rr].valid)
        {
            v = entries[rr].value;
            rr = register_null;
        }
    }
};


class InstructionQueue
{
private:
    std::deque<Instruction*> entries;

public:
    explicit operator bool()
    {
        return !entries.empty();
    }

    bool full()
    {
        return entries.size() == n_fetch;
    }

    bool push(Instruction* instruction)
    {
        entries.push_back(instruction);

        return false;
    }

    Instruction* front()
    {
        return entries.front();
    }

    void pop()
    {
        entries.pop_front();
    }

    void speculation_confirm()
    {
        for (Instruction* entry : entries)
            --entry->speculativeLevel;
    }

    void speculation_deny()
    {
        for (unsigned i(0); i < entries.size();)
            if (entries[i]->speculativeLevel != 0)
                entries.erase(std::begin(entries) + i);
            else
                ++i;
    }
};


class ReservationStation
{
    static const unsigned n_entries{20};

    std::deque<Instruction*> stations;
    unsigned i_station{0};

public:
    operator bool()
    {
        return stations.size() != 0;
    }

    bool full()
    {
        return stations.size() == n_entries;
    }

    void push(Instruction* instructionQueueEntry)
    {
        stations.push_back(instructionQueueEntry);
    }

    bool pop(Instruction*& reservationStationEntry, RegisterStatusTable& registerStatusTable)
    {
        for (; i_station < stations.size(); ++i_station)
        {
            Instruction* instruction(stations[i_station]);
            registerStatusTable.processIssueSourceRegister(instruction->vs, instruction->rrs);
            registerStatusTable.processIssueSourceRegister(instruction->vr, instruction->rrr);
            if (instruction->rrs != register_null || instruction->rrr != register_null)
                continue;
            
            reservationStationEntry = instruction;
            stations.erase(std::begin(stations) + i_station);

            return true;
        }

        i_station = 0;
        return false;
    }

    void speculation_confirm()
    {
        for (Instruction* entry : stations)
            --entry->speculativeLevel;
    }

    void speculation_deny()
    {
        for (unsigned i(0); i < stations.size();)
            if (stations[i]->speculativeLevel != 0)
                stations.erase(std::begin(stations) + i);
            else
                ++i;
    }
};


class IssueBuffer
{
    static const unsigned n_entries{20};

    std::deque<Instruction*> issues;

public:
    operator bool()
    {
        return issues.size() != 0;
    }

    bool full()
    {
        return issues.size() == n_entries;
    }

    void push(Instruction* instructionQueueEntry)
    {
        issues.push_back(instructionQueueEntry);
    }

    Instruction* front()
    {
        return issues.front();
    }

    void pop()
    {
        issues.pop_front();
    }

    void speculation_confirm()
    {
        for (Instruction* entry : issues)
            --entry->speculativeLevel;
    }

    void speculation_deny()
    {
        for (unsigned i(0); i < issues.size();)
            if (issues[i]->speculativeLevel != 0)
                issues.erase(std::begin(issues) + i);
            else
                ++i;
    }
};


class Processor
{
    RegisterFile registerFile;
    InstructionQueue instructionQueue;
    ReservationStation reservationStation;
    RegisterStatusTable registerStatusTable;
    IssueBuffer issueBuffer;

    unsigned pc;
    unsigned nextSpeculativeLevel;
    unsigned clock;
    static const word_t n_memory{256};
    byte_t memory[n_memory];
    word_t* memory_words{(word_t*)(memory)};

    std::multiset<unsigned>
        memory_accesses,
        branches;

public:
    void assign(const Instruction* instruction, word_t v)
    {
        registerStatusTable.entries[instruction->rrd].value = v;
    }

    void branch(word_t pc, signed i, bool taken)
    {
        // This should only be called by conditional branches. Need to check if backwards branch wasn't taken or forwards branch was; sort out speculative level stuff
        if (taken && i < 0 || !taken && i >= 0)
            speculation_confirm();
        else
        {
            speculation_deny();
            if (taken)
                this->pc = pc-1 + i;
            else
                this->pc = pc;
        }
    }

    void call(const Instruction* instruction, word_t pc)
    {
        // Need to set lr as rd in calls to give renamable registers
        assign(instruction, pc);
    }

    void clearPipeline()
    {
    }

    void execute(const Program& program)
    {
        const unsigned n_program(program.size());
        clearPipeline();
        pc = 0;
        clock = n_pipeline;
        nextSpeculativeLevel = 0;
        unsigned i_fetch(n_fetch);


        while (pc < n_program || instructionQueue || reservationStation || issueBuffer)
        {
            // Fetch
            while (pc < n_program && !instructionQueue.full() && nextSpeculativeLevel < n_speculative_levels)
            {
                Instruction* instruction(program[pc++]);
                instruction->speculativeLevel = nextSpeculativeLevel;
                instructionQueue.push(instruction);
                instruction->fetch(); // Actually a predecode
            }

            outputStep("Post-fetch");

            // Dispatch
            while (instructionQueue && !reservationStation.full())
            {
                Instruction* instruction(instructionQueue.front());
                if (instruction->rd != register_null && registerStatusTable.full())
                    break;

                reservationStation.push(instruction);
                instructionQueue.pop();
                registerStatusTable.processDispatchSourceRegister(instruction->rs, instruction->vs, instruction->rrs, instruction->speculativeLevel, registerFile);
                registerStatusTable.processDispatchSourceRegister(instruction->rr, instruction->vr, instruction->rrr, instruction->speculativeLevel, registerFile);
                registerStatusTable.processDispatchDestinationRegister(instruction->rd, instruction->rrd, instruction->speculativeLevel, registerFile);
            }

            outputStep("Post-dispatch");

            // Issue
            {
                Instruction* reservationStationEntry;
                while (!issueBuffer.full() && reservationStation.pop(reservationStationEntry, registerStatusTable))
                    issueBuffer.push(reservationStationEntry);
            }

            outputStep("Post-issue");

            // Execute
            while (issueBuffer)
            {
                Instruction* issue(issueBuffer.front());
                issueBuffer.pop();
                issue->execute();
                if (issue->rrd != register_null)
                    registerStatusTable.entries[issue->rrd].valid = true;
            }

            outputStep("Post-execute");

            // Writeback
            for (unsigned i(0); i < n_speculative_levels; ++i)
                for (unsigned ii(0); ii < n_registers; ++ii)
                {
                    RegisterFile_entry& registerFileEntry(registerFile.entries[i][ii]);
                    RegisterStatusTable::Entry& registerStatusTableEntry(registerStatusTable.entries[registerFileEntry.i_registerStatusTable]);

                    if (registerFileEntry.reserved && registerStatusTableEntry.valid && registerStatusTable.isBusy(registerFileEntry.i_registerStatusTable))
                    {
                        for (unsigned iii(i); iii < n_speculative_levels; ++iii)
                            registerFile.entries[iii][ii].value = registerStatusTableEntry.value;
                        registerFileEntry.value = registerStatusTableEntry.value;
                        registerStatusTable.clearBusy(registerFileEntry.i_registerStatusTable);
                        registerFileEntry.reserved = false;
                    }
                }

            outputStep("Post-writeback");

            ++clock;
            outputState();
        }

        //outputState();
    }

    word_t memory_load(word_t address)
    {
        address %= n_memory;
        memory_accesses.insert(address);
        return memory_words[address / word_size];
    }

    void memory_store(word_t address, word_t value)
    {
        address %= n_memory;
        memory_accesses.insert(address);
        memory_words[address / word_size] = value;
    }

    void outputState()
    {
        std::cout << std::uppercase;

        std::cout
            << "pc: " << std::hex << pc
            << "\nClock: " << std::dec << clock
            << "\nTotal memory accesses: " << std::dec << memory_accesses.size()
            << "\nTotal branches taken: " << std::dec << branches.size()
            << "\n\n";

        for (unsigned i(0); i < n_registers; ++i)
            std::cout << 'r' << std::dec << i << ": " << std::hex << registerFile.entries[0][i].value << '\n';
        std::cout << '\n';

        std::set<unsigned>&& memory_accesses_unique{memory_accesses.begin(), memory_accesses.end()};
        std::vector<unsigned> addresses{memory_accesses_unique.begin(), memory_accesses_unique.end()};
        std::sort(addresses.begin(), addresses.end());
        for (unsigned address : addresses)
            std::cout << std::hex << "memory[" << address << "] = " << memory_words[address / word_size] << '\n';

        std::cout << "\n--------------------------------\n\n";
    }

    void outputStep(const char text[])
    {
#if 0
        std::cout << text << '\n';

        for (RegisterFile_entry& registerFileEntry : registerFile.entries)
        {
            const unsigned
                i_registerStatusTable(registerFileEntry.i_registerStatusTable),
                i_speculativeLevel(registerFileEntry.i_speculativeLevel);

            std::cout << std::boolalpha
                << registerFileEntry.value[i_speculativeLevel] << ": "
                << registerFileEntry.reserved << ", (" << i_registerStatusTable << ", " << i_speculativeLevel << "), "
                << registerStatusTable.isValid(i_speculativeLevel, i_registerStatusTable) << ", " << registerStatusTable.isBusy(i_speculativeLevel, i_registerStatusTable)
                << ", " << registerStatusTable.value[i_speculativeLevel][i_registerStatusTable]
                << '\n';
        }
        std::cout << '\n';
#endif
    }

    word_t predictBranch(unsigned branch_target_in, unsigned mode, bool unconditional, unsigned speculativeLevel)
    {
        // mode 0 absolute
        // mode 1 relative
        // mode 2 register

        word_t old_pc = pc;

        unsigned branch_target;
        if (mode == 0)
            branch_target = branch_target_in;
        else if (mode == 1)
            branch_target = pc - 1 + branch_target_in;
        else
        {
            RegisterFile_entry& registerFileEntry(registerFile.entries[speculativeLevel][branch_target_in]);
            RegisterStatusTable::Entry& registerStatusTableEntry(registerStatusTable.entries[branch_target_in]);
            if (!registerFileEntry.reserved || !registerStatusTableEntry.valid)
                branch_target = registerFileEntry.value;
            else
                branch_target = registerStatusTableEntry.value;
        }

        if (unconditional && mode != 2 || mode == 1 && branch_target < pc)
            pc = branch_target;
        
        if (!unconditional)
            speculation_increment();

        if (mode == 2)
            return branch_target;

        return old_pc;
    }

    void ret(const Instruction* instruction, word_t predictedAddress)
    {
        if (instruction->vs == predictedAddress)
            speculation_confirm();
        else
            speculation_deny();

        pc = instruction->vs;
    }

    void speculation_confirm()
    {
        --nextSpeculativeLevel;

        instructionQueue.speculation_confirm();
        reservationStation.speculation_confirm();
        issueBuffer.speculation_confirm();

        registerFile.speculation_confirm();
        registerStatusTable.speculation_confirm();
    }

    void speculation_deny()
    {
        nextSpeculativeLevel = 0;
        clock += n_pipeline;

        instructionQueue.speculation_deny();
        reservationStation.speculation_deny();
        issueBuffer.speculation_deny();

        registerFile.speculation_deny();
        registerStatusTable.speculation_deny();
    }
    
    void speculation_increment()
    {
        ++nextSpeculativeLevel;
        if (nextSpeculativeLevel == n_speculative_levels)
            return;
    }
};


// Common binary instructions
#if 1
#define instruction(name, op)                                  \
class name : public Instruction                                \
{                                                              \
protected:                                                     \
    unsigned i;                                                \
    address_mode_t addressMode;                                \
                                                               \
public:                                                        \
    name(unsigned rd_in, unsigned rs_in, const unsigned& rr_in)\
        : addressMode(reg)                                     \
    {                                                          \
        rd = rd_in;                                            \
        rs = rs_in;                                            \
        rr = rr_in;                                            \
    }                                                          \
                                                               \
    name(unsigned rd_in, unsigned rs_in, const unsigned&& i)   \
        : i(i), addressMode(imm)                               \
    {                                                          \
        rd = rd_in;                                            \
        rs = rs_in;                                            \
    }                                                          \
                                                               \
    virtual void execute() const override                      \
    {                                                          \
        switch (addressMode)                                   \
        {                                                      \
        case reg:                                              \
            processor->assign(this, vs op vr);                 \
            break;                                             \
        case imm:                                              \
            processor->assign(this, vs op i);                  \
        }                                                      \
    }                                                          \
};

instruction(add, +)
instruction(sub, -)
instruction(mul, *)
instruction(andd, &)
instruction(orr, |)
instruction(xorr, ^)
instruction(lsl, <<)
instruction(lsr, >>)
#undef instruction


class mov : public Instruction
{
protected:
    unsigned i;
    address_mode_t addressMode;
 
public:
    mov(unsigned rd_in, const unsigned& rs_in)
        : addressMode(reg)
    {
        rd = rd_in;
        rs = rs_in;
    }
 
    mov(unsigned rd_in, const unsigned&& i)
        : i(i), addressMode(imm)
    {
        rd = rd_in;
    }

    virtual void execute() const override
    {
        switch (addressMode)
        {
        case reg:
            processor->assign(this, vs);
            break;
        case imm:
            processor->assign(this, i);
        }
    }
};
#endif


// Branch instructions
#if 1
#define instruction(name, op)                                        \
class name : public Instruction                                      \
{                                                                    \
protected:                                                           \
    signed x;                                                        \
    signed i;                                                        \
    address_mode_t addressMode;                                      \
    word_t pc;                                                       \
                                                                     \
public:                                                              \
    name(signed i, unsigned rs_in, unsigned& rr_in)                  \
        : i(i), addressMode(reg)                                     \
    {                                                                \
        rs = rs_in;                                                  \
        rr = rr_in;                                                  \
    }                                                                \
                                                                     \
    name(signed i, unsigned rs_in, signed&& x)                       \
        : i(i), x(x), addressMode(imm)                               \
    {                                                                \
        rs = rs_in;                                                  \
    }                                                                \
                                                                     \
    virtual void execute() const override                            \
    {                                                                \
        switch (addressMode)                                         \
        {                                                            \
        case reg:                                                    \
            processor->branch(pc, i, signed(vs) op signed(vr));      \
            break;                                                   \
        case imm:                                                    \
            processor->branch(pc, i, signed(vs) op x);               \
        }                                                            \
    }                                                                \
                                                                     \
    virtual void fetch() override                                    \
    {                                                                \
        pc = processor->predictBranch(i, 1, false, speculativeLevel);\
    }                                                                \
};

instruction(ble, <=)
instruction(blt, <)
instruction(beq, ==)
instruction(bne, !=)
instruction(bgt, >)
instruction(bge, >=)
#undef instruction

class b : public Instruction
{
protected:
    signed i;

public:
    b(signed i)
        : i(i)
    {}

    virtual void execute() const override
    {}

    virtual void fetch() override
    {
        processor->predictBranch(i, 1, true, speculativeLevel);
    }
};

class call : public Instruction
{
protected:
    const word_t address;
    word_t pc;

public:
    call(const word_t address)
        : address(address)
    {
        rd = lr;
    }

    virtual void execute() const override
    {
        processor->call(this, pc);
    }

    virtual void fetch() override
    {
        pc = processor->predictBranch(address, 0, true, speculativeLevel);
    }
};

class ret : public Instruction
{
    word_t predictedAddress;

public:
    ret()
    {
        rs = lr;
    }

    virtual void execute() const override
    {
        processor->ret(this, predictedAddress);
    }

    virtual void fetch() override
    {
        predictedAddress = processor->predictBranch(lr, 2, false, speculativeLevel);
    }
};
#endif


// Memory instructions
// Maybe overload operand for constant store
#if 1
class ldr : public Instruction
{
public:
    ldr(unsigned rd_in, unsigned rs_in)
    {
        rd = rd_in;
        rs = rs_in;
    }

    virtual void execute() const override
    {
        processor->assign(this, processor->memory_load(vs));
    }
};

class str : public Instruction
{
public:
    str(unsigned rs_in, unsigned rr_in)
    {
        rs = rs_in;
        rr = rr_in;
    }

    virtual void execute() const override
    {
        processor->memory_store(vs, vr);
    }
};
#endif


int main()
{
    Processor processor;
    unsigned r[n_registers];
    std::iota(std::begin(r), std::end(r), 0);

    Program superscalarTest
    {
        {
            new b(3),
            new mov(r[0], 8),
            new b(3),
            new mov(r[0], 0),
            new beq(-3, r[0], 0)
        },
        processor
    };
    processor.execute(superscalarTest);

    Program subroutineTest
    {
        {
            new b(4 /*main_start*/),
            // subroutine_start
            new mov(r[0], 1),
            new mov(r[1], 2),
            new ret,
            // subroutine_end
            // main_begin
            new call(1)
            // main_end
        },
        processor
    };
    //processor.execute(subroutineTest);

    Program simple_sort
    {
/*
void leftPartition(int a[], n_t n)
{
    for (index_t r(0); r < n; ++r)
        for (index_t l(0); l < r; ++l)
            if (a[r] < a[l])
                std::swap(a[r], a[l]);
}
*/
        {
            // init_memory
#if 1
            new mov(r[1], 0),
            new mov(r[0], 5),
            new str(r[1], r[0]),
            new add(r[1], r[1], std::move(word_size)),
            new mov(r[0], 3),
            new str(r[1], r[0]),
            new add(r[1], r[1], std::move(word_size)),
            new mov(r[0], 4),
            new str(r[1], r[0]),
            new add(r[1], r[1], std::move(word_size)),
            new mov(r[0], 2),
            new str(r[1], r[0]),
            new add(r[1], r[1], std::move(word_size)),
            new mov(r[0], 1),
            new str(r[1], r[0]),
            new mov(r[6], 0), // a
            new mov(r[7], 5), // n
#endif
            // end_init_memory

            new mul(r[7], r[7], std::move(word_size)),
            new mov(r[5], 0),
            new bge(14 /*loop_alpha_end*/, r[5], r[7]),
            // loop_alpha_start
                new mov(r[4], 0),
                new bge(10 /*loop_beta_end*/, r[4], r[5]),
                // loop_beta_start
                    new add(r[2], r[6], r[5]),
                    new ldr(r[1], r[2]),
                    new add(r[3], r[6], r[4]),
                    new ldr(r[0], r[3]),
                    new bge(3 /*swap_end*/, r[1], r[0]),
                        new str(r[3], r[1]),
                        new str(r[2], r[0]),
                    // swap_end
                    new add(r[4], r[4], std::move(word_size)),
                    new blt(-8 /*loop_beta_start*/, r[4], r[5]),
                // loop_beta_end
                new add(r[5], r[5], std::move(word_size)),
                new blt(-12 /*loop_alpha_start*/, r[5], r[7])
            // loop_alpha_end
        },
        processor
    };
    //processor.execute(simple_sort);
}

#ifndef _witness_stack_hpp_INCLUDED
#define _witness_stack_hpp_INCLUDED

#include <cassert>
#include <cstdint>
#include <cstddef>
#include <cstdlib>
#include <cstring>

namespace CaDiCaL {

// Arena for smaller witness stacks
//
// A common case are stacks that contain two binary or one ternary clause.
// For two binary clauses we commonly need 8 integers:
// size | capacity | S | idl | S | S' | idl' | S' 
// For one ternay clause we commonly need 6 integers : 
// size | capacity | S | idl | l_o | S

struct WitnessArena { 

	static constexpr unsigned NUM_CLASSES = 6;

	static constexpr unsigned BLOCKS_PER_CHUNK = 4096;

	struct Stats {
    uint64_t allocations[NUM_CLASSES] = {};
    uint64_t deallocations[NUM_CLASSES] = {};

    uint64_t chunks[NUM_CLASSES] = {};

    uint64_t live[NUM_CLASSES] = {};
    uint64_t peak_live[NUM_CLASSES] = {};

    uint64_t large_allocations = 0;
    uint64_t large_deallocations = 0;

    uint64_t growths[NUM_CLASSES] = {};

    uint64_t shrink_count = 0;
    uint64_t shrink_bytes_saved = 0;

    uint64_t peak_reserved_bytes = 0;
	};

	struct Block {
		Block *next;
	};

	struct Chunk {
		Chunk *next;
	};

	struct SizeClass {
		unsigned capacity;
		Block *free_list;
		Chunk *chunks;
	};

	SizeClass classes[NUM_CLASSES];

	Stats stats;

	~WitnessArena () {
    for (unsigned i = 0; i < NUM_CLASSES; i++)
    	release_chunks (classes[i]);
	}

	WitnessArena () {
    classes[0] = { 8,   nullptr, nullptr };
    classes[1] = { 12,  nullptr, nullptr };
    classes[2] = { 16,  nullptr, nullptr };
    classes[3] = { 32,  nullptr, nullptr };
    classes[4] = { 64,  nullptr, nullptr };
    classes[5] = { 128, nullptr, nullptr };
	}

	WitnessArena (const WitnessArena &) = delete;
	WitnessArena &operator= (const WitnessArena &) = delete;

	int *allocate (unsigned capacity) {
		const std::size_t bytes = static_cast<std::size_t> (capacity) * sizeof (int);
		const unsigned index = class_index (capacity);

		if (index == NUM_CLASSES) {
			// Large allocation: bypass the arena.
			int *result = static_cast<int *> (std::malloc (bytes));
			assert (result);

			stats.large_allocations++;
			return result;
		}

		SizeClass &sc = classes[index];

		if (!sc.free_list)
			add_chunk (sc);
		
		assert (sc.free_list);

		Block *block = sc.free_list;
		sc.free_list = block->next;

		stats.allocations[index]++;
		stats.live[index]++;
		if (stats.live[index] > stats.peak_live[index])
			stats.peak_live[index] = stats.live[index];

		return reinterpret_cast<int *> (block);
	}

	void deallocate (int *ptr, unsigned capacity) {
		if (!ptr)
			return;

		const unsigned index = class_index (capacity);

		if (index == NUM_CLASSES) {
			std::free (ptr);
			stats.large_deallocations++;
			return;
		}

		SizeClass &sc = classes[index];

		Block *block = reinterpret_cast<Block *> (ptr);

		block->next = sc.free_list;
		sc.free_list = block;

		assert (stats.live[index] > 0);
		stats.deallocations[index]++;
		stats.live[index]--;
	}

	void record_growth (unsigned old_capacity) {
		const unsigned index = class_index (old_capacity);
		if (index < NUM_CLASSES)
			stats.growths[index]++;
	}

	uint64_t reserved_bytes () const {
		uint64_t result = 0;

		for (unsigned i = 0; i < NUM_CLASSES; ++i)
			result += static_cast<uint64_t> (stats.chunks[i]) * (sizeof (Chunk) + 
								static_cast<uint64_t> (BLOCKS_PER_CHUNK) * 
								classes[i].capacity * sizeof (int));
		
		return result;
	}

	unsigned find_size_class (unsigned requested) const {
		if (requested <= 8) return 8;
		if (requested <= 12) return 12;
		if (requested <= 16) return 16;
		if (requested <= 32) return 32;
		if (requested <= 64) return 64;
		if (requested <= 128) return 128;
		return requested;
	}

private:

	unsigned class_index (unsigned capacity) const {
		switch (capacity) {
		case 8: return 0;
		case 12: return 1;
		case 16: return 2;
		case 32: return 3;
		case 64: return 4;
		case 128: return 5;
		default: return NUM_CLASSES;
		}
	}

	void add_chunk (SizeClass &sc) {
		const std::size_t block_size = sc.capacity * sizeof (int);

		const std::size_t chunk_size = sizeof (Chunk) + BLOCKS_PER_CHUNK * block_size;

		Chunk *chunk = static_cast<Chunk *> (std::malloc (chunk_size));

		assert (chunk);

		const unsigned index = class_index (sc.capacity);
		assert (index < NUM_CLASSES);
		stats.chunks[index]++;

		chunk->next = sc.chunks;
		sc.chunks = chunk;

		char *memory = reinterpret_cast<char *> (chunk) + sizeof (Chunk);

		// Turn the entire chunk into a free list.
		Block *previous = nullptr;

		for (unsigned i = 0; i < BLOCKS_PER_CHUNK; ++i) {
			Block *block = reinterpret_cast<Block *> (memory + i * block_size);

			block->next = previous;
			previous = block;
		}

		sc.free_list = previous;

		// New chunk has increased reserved memory.
		const uint64_t reserved = reserved_bytes ();
		if (reserved > stats.peak_reserved_bytes)
			stats.peak_reserved_bytes = reserved;
	}

	void release_chunks (SizeClass &sc) {
		Chunk *chunk = sc.chunks;

		while (chunk) {
			Chunk *next = chunk->next;
			std::free (chunk);
			chunk = next;
		}

		sc.chunks = nullptr;
		sc.free_list = nullptr;
	}
};

// Dynamic array for weakened clauses with a given witness. 
// The stack just consists of a int*. Size and capacity are stored in the 
// first two places of the array. 

struct WitnessStack {
	int *stack = nullptr;

	unsigned size () const {
		return stack ? static_cast<unsigned> (stack[0]) : 0;
	}

	unsigned capacity () const {
		return stack ? static_cast<unsigned> (stack[1]) : 0;
	}

	bool empty () const {
		return size () == 0;
	}

	void allocate (unsigned requested, WitnessArena &arena) {
		assert (!stack);
		assert (requested >= 2);

		const unsigned cap = arena.find_size_class (requested);

		stack = arena.allocate (cap);

		stack[0] = 2;
		stack[1] = cap;
	}

	void push_back (int val, WitnessArena &arena) {
		if (!stack) { // empty stack <-> nullptr
			allocate (8, arena); // common case
		} else if (stack[0] == stack[1]) { // stack is full. Grow...
			grow (arena);
		}
		const unsigned old_size = size (); // old size (also idx to end)
		stack[old_size] = val; // store value at end of stack
		stack[0] = old_size + 1; // increment size
	}

	void grow (WitnessArena &arena) {
		assert (stack);
		assert (stack[0] == stack[1]);

		const unsigned old_size = size ();
		const unsigned old_cap  = capacity ();

		unsigned new_cap;

		switch (old_cap) {
		case 8: new_cap = 12; break;
		case 12: new_cap = 16; break;
		default: new_cap = 2 * old_cap; break;
		}

		int *new_stack = arena.allocate (new_cap);

		std::memcpy (new_stack, stack, old_size * sizeof (int));
		new_stack[1] = new_cap;

		arena.deallocate (stack, old_cap);
		stack = new_stack;

		arena.record_growth (old_cap);
	}

	void truncate (unsigned new_size, WitnessArena &arena) {
		assert (stack);
		assert (new_size >= 2);
		assert (new_size <= size ());

		if (new_size == 2) {
			clear (arena);
			return;
		}

		stack[0] = new_size;
	}

	void shrink_to_fit (WitnessArena &arena) {
		if (!stack || size () == capacity ())
			return;

		const unsigned old_size = size ();
		const unsigned old_cap = capacity ();

		int *new_stack = arena.allocate (old_size);

		std::memcpy (new_stack, stack, old_size * sizeof (int));
		new_stack[1] = old_size;

		arena.deallocate (stack, old_cap);
		stack = new_stack;

		arena.stats.shrink_count++;
		arena.stats.shrink_bytes_saved += (old_cap - old_size) * sizeof (int);
	}

	void clear (WitnessArena &arena) {
		if (!stack)
			return;	
		const unsigned old_cap = capacity ();

		assert (old_cap >= 2);
    assert (stack[0] >= 2);
    assert (static_cast<unsigned>(stack[0]) <= old_cap);

		arena.deallocate (stack, old_cap);
		stack = nullptr;
	}
	
	int *begin () {
	    return stack ? stack + 2 : nullptr;
	}

	const int *begin () const {
	    return stack ? stack + 2 : nullptr;
	}

	int *end () {
	    return stack ? stack + stack[0] : nullptr;
	}

	const int *end () const {
	    return stack ? stack + stack[0] : nullptr;
	}

	int &operator[] (uint32_t i) {
		assert (stack);
		assert (i < size () - 2);
		return stack[i + 2]; // skip size and capacity
	}

	const int &operator[] (uint32_t i) const {
		assert (stack);
		assert (i < size () - 2);
		return stack[i + 2];
	}
};


struct CubeStackChunk {
	std::vector<WitnessStack> stacks;
	uint32_t free_list = UINT32_MAX;

	uint32_t allocate () {
		if (free_list != UINT32_MAX) {
			const uint32_t index = free_list;
			free_list = static_cast<uint32_t> (reinterpret_cast<uintptr_t> (stacks[index].stack));
			stacks[index].stack = nullptr;
			return index;
		}

		stacks.emplace_back ();
		return static_cast<uint32_t> (stacks.size () - 1);
	}

	void deallocate (uint32_t index) {
		assert (index < stacks.size ());
		assert (stacks[index].stack);
		stacks[index].stack = reinterpret_cast<int *> (static_cast<uintptr_t> (free_list));
		free_list = index;
	}

	WitnessStack &operator[] (uint32_t index) {
  	assert (index < stacks.size ());
  	return stacks[index];
	}

	const WitnessStack &operator[] (uint32_t index) const {
  	assert (index < stacks.size ());
  	return stacks[index];
	}
};


} // namespace CaDiCaL
#endif
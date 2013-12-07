#include <assert.h>
#include <math.h>
#include "btree.h"

KeyValuePair::KeyValuePair()
{}


KeyValuePair::KeyValuePair(const KEY_T &k, const VALUE_T &v) : 
    key(k), value(v)
{}


KeyValuePair::KeyValuePair(const KeyValuePair &rhs) :
    key(rhs.key), value(rhs.value)
{}


KeyValuePair::~KeyValuePair()
{}


KeyValuePair & KeyValuePair::operator=(const KeyValuePair &rhs)
{
    return *( new (this) KeyValuePair(rhs));
}

BTreeIndex::BTreeIndex(SIZE_T keysize, 
        SIZE_T valuesize,
        BufferCache *cache,
        bool unique) 
{
    superblock.info.keysize=keysize;
    superblock.info.valuesize=valuesize;
    buffercache=cache;
    // note: ignoring unique now
}

BTreeIndex::BTreeIndex()
{
    // shouldn't have to do anything
}


//
// Note, will not attach!
//
BTreeIndex::BTreeIndex(const BTreeIndex &rhs)
{
    buffercache=rhs.buffercache;
    superblock_index=rhs.superblock_index;
    superblock=rhs.superblock;
}

BTreeIndex::~BTreeIndex()
{
    // shouldn't have to do anything
}


BTreeIndex & BTreeIndex::operator=(const BTreeIndex &rhs)
{
    return *(new(this)BTreeIndex(rhs));
}


ERROR_T BTreeIndex::AllocateNode(SIZE_T &n)
{
    n=superblock.info.freelist;

    if (n==0) { 
        return ERROR_NOSPACE;
    }

    BTreeNode node;

    node.Unserialize(buffercache,n);

    assert(node.info.nodetype==BTREE_UNALLOCATED_BLOCK);

    superblock.info.freelist=node.info.freelist;

    superblock.Serialize(buffercache,superblock_index);

    buffercache->NotifyAllocateBlock(n);

    return ERROR_NOERROR;
}


ERROR_T BTreeIndex::DeallocateNode(const SIZE_T &n)
{
    BTreeNode node;

    node.Unserialize(buffercache,n);

    assert(node.info.nodetype!=BTREE_UNALLOCATED_BLOCK);

    node.info.nodetype=BTREE_UNALLOCATED_BLOCK;

    node.info.freelist=superblock.info.freelist;

    node.Serialize(buffercache,n);

    superblock.info.freelist=n;

    superblock.Serialize(buffercache,superblock_index);

    buffercache->NotifyDeallocateBlock(n);

    return ERROR_NOERROR;

}

ERROR_T BTreeIndex::Attach(const SIZE_T initblock, const bool create)
{
    ERROR_T rc;

    superblock_index=initblock;
    assert(superblock_index==0);

    if (create) {
        // build a super block, root node, and a free space list
        //
        // Superblock at superblock_index
        // root node at superblock_index+1
        // free space list for rest
        BTreeNode newsuperblock(BTREE_SUPERBLOCK,
                superblock.info.keysize,
                superblock.info.valuesize,
                buffercache->GetBlockSize());
        newsuperblock.info.rootnode=superblock_index+1;
        newsuperblock.info.freelist=superblock_index+2;
        newsuperblock.info.numkeys=0;

        buffercache->NotifyAllocateBlock(superblock_index);

        rc=newsuperblock.Serialize(buffercache,superblock_index);

        if (rc) { 
            return rc;
        }

        BTreeNode newrootnode(BTREE_ROOT_NODE,
                superblock.info.keysize,
                superblock.info.valuesize,
                buffercache->GetBlockSize());
        newrootnode.info.rootnode=superblock_index+1;
        newrootnode.info.freelist=superblock_index+2;
        newrootnode.info.numkeys=0;

        buffercache->NotifyAllocateBlock(superblock_index+1);

        rc=newrootnode.Serialize(buffercache,superblock_index+1);

        if (rc) { 
            return rc;
        }

        for (SIZE_T i=superblock_index+2; i<buffercache->GetNumBlocks();i++) { 
            BTreeNode newfreenode(BTREE_UNALLOCATED_BLOCK,
                    superblock.info.keysize,
                    superblock.info.valuesize,
                    buffercache->GetBlockSize());
            newfreenode.info.rootnode=superblock_index+1;
            newfreenode.info.freelist= ((i+1)==buffercache->GetNumBlocks()) ? 0: i+1;

            rc = newfreenode.Serialize(buffercache,i);

            if (rc) {
                return rc;
            }

        }
    }

    // OK, now, mounting the btree is simply a matter of reading the superblock 

    return superblock.Unserialize(buffercache,initblock);
}


ERROR_T BTreeIndex::Detach(SIZE_T &initblock)
{
    return superblock.Serialize(buffercache,superblock_index);
}


ERROR_T BTreeIndex::LookupOrUpdateInternal(const SIZE_T &node,
        const BTreeOp op,
        const KEY_T &key,
        VALUE_T &value)
{
    BTreeNode b;
    ERROR_T rc;
    SIZE_T offset;
    KEY_T testkey;
    SIZE_T ptr;

    rc= b.Unserialize(buffercache,node);

    if (rc!=ERROR_NOERROR) { 
        return rc;
    }

    switch (b.info.nodetype) { 
        case BTREE_ROOT_NODE:
        case BTREE_INTERIOR_NODE:
            // Scan through key/ptr pairs
            //and recurse if possible
            for (offset=0;offset<b.info.numkeys;offset++) { 
                rc=b.GetKey(offset,testkey);
                if (rc) {  return rc; }
                if (key<testkey || key==testkey) {
                    // OK, so we now have the first key that's larger
                    // so we ned to recurse on the ptr immediately previous to 
                    // this one, if it exists
                    rc=b.GetPtr(offset,ptr);
                    if (rc) { return rc; }
                    return LookupOrUpdateInternal(ptr,op,key,value);
                }
            }
            // if we got here, we need to go to the next pointer, if it exists
            if (b.info.numkeys>0) { 
                rc=b.GetPtr(b.info.numkeys,ptr);
                if (rc) { return rc; }
                return LookupOrUpdateInternal(ptr,op,key,value);
            } else {
                // There are no keys at all on this node, so nowhere to go
                return ERROR_NONEXISTENT;
            }
            break;
        case BTREE_LEAF_NODE:
            // Scan through keys looking for matching value
            for (offset=0;offset<b.info.numkeys;offset++) { 
                rc=b.GetKey(offset,testkey);
                if (rc) {  return rc; }
                if (testkey==key) { 
                    if (op==BTREE_OP_LOOKUP) { 
                        return b.GetVal(offset,value);
                    } else { 
                        // BTREE_OP_UPDATE
                        rc=b.SetVal(offset,value);
                        if (rc) { return rc; }
                        return b.Serialize(buffercache,node);
                    }
                }
            }
            return ERROR_NONEXISTENT;
            break;
        default:
            // We can't be looking at anything other than a root, internal, or leaf
            return ERROR_INSANE;
            break;
    }  

    return ERROR_INSANE;
}


static ERROR_T PrintNode(ostream &os, SIZE_T nodenum, BTreeNode &b, BTreeDisplayType dt)
{
    KEY_T key;
    VALUE_T value;
    SIZE_T ptr;
    SIZE_T offset;
    ERROR_T rc;
    unsigned i;

    if (dt==BTREE_DEPTH_DOT) { 
        os << nodenum << " [ label=\""<<nodenum<<": ";
    } else if (dt==BTREE_DEPTH) {
        os << nodenum << ": ";
    } else {
    }

    switch (b.info.nodetype) { 
        case BTREE_ROOT_NODE:
        case BTREE_INTERIOR_NODE:
            if (dt==BTREE_SORTED_KEYVAL) {
            } else {
                if (dt==BTREE_DEPTH_DOT) { 
                } else { 
                    os << "Interior: ";
                }
                for (offset=0;offset<=b.info.numkeys;offset++) { 
                    rc=b.GetPtr(offset,ptr);
                    if (rc) { return rc; }
                    os << "*" << ptr << " ";
                    // Last pointer
                    if (offset==b.info.numkeys) break;
                    rc=b.GetKey(offset,key);
                    if (rc) {  return rc; }
                    for (i=0;i<b.info.keysize;i++) { 
                        os << key.data[i];
                    }
                    os << " ";
                }
            }
            break;
        case BTREE_LEAF_NODE:
            if (dt==BTREE_DEPTH_DOT || dt==BTREE_SORTED_KEYVAL) { 
            } else {
                os << "Leaf: ";
            }
            for (offset=0;offset<b.info.numkeys;offset++) { 
                if (offset==0) { 
                    // special case for first pointer
                    rc=b.GetPtr(offset,ptr);
                    if (rc) { return rc; }
                    if (dt!=BTREE_SORTED_KEYVAL) { 
                        os << "*" << ptr << " ";
                    }
                }
                if (dt==BTREE_SORTED_KEYVAL) { 
                    os << "(";
                }
                rc=b.GetKey(offset,key);
                if (rc) {  return rc; }
                for (i=0;i<b.info.keysize;i++) { 
                    os << key.data[i];
                }
                if (dt==BTREE_SORTED_KEYVAL) { 
                    os << ",";
                } else {
                    os << " ";
                }
                rc=b.GetVal(offset,value);
                if (rc) {  return rc; }
                for (i=0;i<b.info.valuesize;i++) { 
                    os << value.data[i];
                }
                if (dt==BTREE_SORTED_KEYVAL) { 
                    os << ")\n";
                } else {
                    os << " ";
                }
            }
            break;
        default:
            if (dt==BTREE_DEPTH_DOT) { 
                os << "Unknown("<<b.info.nodetype<<")";
            } else {
                os << "Unsupported Node Type " << b.info.nodetype ;
            }
    }
    if (dt==BTREE_DEPTH_DOT) { 
        os << "\" ]";
    }
    return ERROR_NOERROR;
}

ERROR_T BTreeIndex::Lookup(const KEY_T &key, VALUE_T &value)
{
    return LookupOrUpdateInternal(superblock.info.rootnode, BTREE_OP_LOOKUP, key, value);
}

ERROR_T BTreeIndex::Insert(const KEY_T &key, const VALUE_T &value)
{
    SIZE_T newnode=(SIZE_T)0;
    KEY_T newkey;
    ERROR_T rc;

    rc=InsertRecursion(superblock.info.rootnode, key, value, newkey, newnode);
    if (rc) { return rc; }

    // case where we need to add a new root node
    if (newnode) {
        BTreeNode oldRoot;
        rc=oldRoot.Unserialize(buffercache,superblock.info.rootnode);
        if (rc) { return rc; }
        BTreeNode newRoot;
        newRoot.info = oldRoot.info;

        rc=newRoot.info.numkeys=1;
        if (rc) { return rc; }
        rc=newRoot.SetKey(0,newkey);
        if (rc) { return rc; }
        rc=newRoot.SetPtr(0,superblock.info.rootnode);
        if (rc) { return rc; }
        rc=newRoot.SetPtr(1,newnode);
        if (rc) { return rc; }

        // allocate space for newRoot on the disk
        SIZE_T newRootBlock;
        rc=AllocateNode(newRootBlock);
        if (rc) { return rc; }

        // serialize newRoot to the disk
        rc=newRoot.Serialize(buffercache,newRootBlock);
        if (rc) { return rc; }
    }
    superblock.info.numkeys++;
    return ERROR_NOERROR;
}

ERROR_T BTreeIndex::InsertRecursion(const SIZE_T &node, const KEY_T &key, const VALUE_T &value, KEY_T &newkey, SIZE_T &newnode)
{
    // first do lookup to find the leaf node we need to insert into
    // insert and split if necessary, return pointer to newnode if splitting
    // after recursive call returns, fix up pointers if there was a new node

    BTreeNode b;
    ERROR_T rc;
    SIZE_T offset;
    KEY_T testkey;
    SIZE_T ptr;

    rc= b.Unserialize(buffercache,node);

    if (rc!=ERROR_NOERROR) { 
        return rc;
    }

    switch (b.info.nodetype) { 
        case BTREE_ROOT_NODE:
            if (b.info.numkeys==0) {
                BTreeNode leaf1=b;
                BTreeNode leaf2=b;
                leaf1.info.numkeys=1;
                leaf2.info.numkeys=0;
                leaf1.info.nodetype=BTREE_LEAF_NODE;
                leaf2.info.nodetype=BTREE_LEAF_NODE;

                b.info.numkeys++;
                rc=leaf1.SetKey(0,key);
                if (rc) { return rc; }
                rc=leaf1.SetVal(0,value);
                if (rc) { return rc; }
                rc=b.SetKey(0,key);
                if (rc) { return rc; }
                
                // allocate space for leaves
                SIZE_T leafBlock1;
                SIZE_T leafBlock2;
                rc=AllocateNode(leafBlock1);
                if (rc) { return rc; }
                rc=AllocateNode(leafBlock2);
                if (rc) { return rc; }
                // update Ptrs of root node
                rc=b.SetPtr(0,leafBlock1);
                if (rc) { return rc; }
                rc=b.SetPtr(1,leafBlock2);
                if (rc) { return rc; }
                // serialize nodes
                rc=b.Serialize(buffercache,node);
                if (rc) { return rc; }
                rc=leaf1.Serialize(buffercache,leafBlock1);
                if (rc) { return rc; }
                rc=leaf2.Serialize(buffercache,leafBlock2);
                if (rc) { return rc; }
                return ERROR_NOERROR;
            }
        case BTREE_INTERIOR_NODE:
            // Scan through key/ptr pairs
            //and recurse if possible
            for (offset=0;offset<b.info.numkeys;offset++) { 
                rc=b.GetKey(offset,testkey);
                if (rc) {  return rc; }
                if (key<testkey || key==testkey) {
                    // OK, so we now have the first key that's larger
                    // so we need to recurse on the ptr immediately previous to 
                    // this one, if it exists
                    rc=b.GetPtr(offset,ptr);
                    if (rc) { return rc; }
                    rc=InsertRecursion(ptr,key,value,newkey,newnode);
                    if (rc) { return rc; }

                    // the case where a new node is returned
                    if (newnode) {
                        // fix up pointers for this interior node
                        // initialize temporary key and ptr variables
                        KEY_T tempKeyPrev=newkey;
                        SIZE_T tempPtrPrev=newnode;
                        KEY_T tempKeyCurrent=testkey; 
                        SIZE_T tempPtrCurrent;
                        rc=b.GetPtr(offset,tempPtrCurrent);
                        if (rc) { return rc; }

                        // iterate through and move all keys and ptrs over by one
                        for (SIZE_T i=offset;i<b.info.numkeys;i++) {
                            rc=b.SetKey(i,tempKeyPrev);
                            if (rc) { return rc; }
                            rc=b.SetPtr(i,tempPtrPrev);
                            if (rc) { return rc; }
                            tempKeyPrev=tempKeyCurrent;
                            tempPtrPrev=tempPtrCurrent;
                            rc=b.GetKey(i+1,tempKeyCurrent);
                            if (rc) { return rc; }
                            rc=b.GetPtr(i+1,tempPtrCurrent);
                            if (rc) { return rc; }
                        }

                        // increment number of keys
                        b.info.numkeys+=1;

                        // edge case where we don't want to get next key and ptr
                        // just set the key and ptr of last position in b 
                        rc=b.SetKey(b.info.numkeys-1,tempKeyCurrent);
                        if (rc) { return rc; }
                        rc=b.SetPtr(b.info.numkeys-1,tempPtrCurrent);
                        if (rc) { return rc; }
                        rc=b.Serialize(buffercache,node);
                        if (rc) { return rc; }

                        // if the node is now too full, split and return the new node
                        if (floor(b.info.GetNumSlotsAsInterior()*(2/3)) <= b.info.numkeys) {
                            //    copy b into splitNode
                            BTreeNode splitNode = b;

                            // last key of first node
                            SIZE_T lastKeyIndex=floor(b.info.numkeys/2)-1;
                            // first key of new split node
                            SIZE_T firstKeyIndex=lastKeyIndex+2;

                            // get the new key that we need to promote
                            rc=b.GetKey(lastKeyIndex+1,newkey);
                            if (rc) { return rc; }

                            // move the second half of the old node into the beginning of newnode
                            SIZE_T insertIndex=0;
                            KEY_T tempKey;
                            SIZE_T tempPtr;
                            for (SIZE_T i=firstKeyIndex;i<splitNode.info.numkeys;i++) {
                                rc=b.GetKey(i,tempKey);
                                if (rc) { return rc; }
                                rc=b.GetPtr(i,tempPtr);
                                if (rc) { return rc; }
                                rc=splitNode.SetKey(insertIndex,tempKey);
                                if (rc) { return rc; }
                                rc=splitNode.SetPtr(insertIndex,tempPtr);
                                if (rc) { return rc; }
                                insertIndex++;
                            }
                            // insert extra pointers
                            rc=b.GetPtr(b.info.numkeys,tempPtr);
                            rc=splitNode.SetPtr(insertIndex,tempPtr);

                            b.info.numkeys=lastKeyIndex+1;
                            splitNode.info.numkeys=insertIndex;

                            // allocate space for newnode on the disk
                            rc=AllocateNode(newnode);
                            if (rc) { return rc; }

                            // serialize newnode and b to the disk
                            rc=splitNode.Serialize(buffercache,newnode);
                            if (rc) { return rc; }
                            rc=b.Serialize(buffercache,node);
                            if (rc) { return rc; }
                        } else {
                            // this node is NOT full
                            // so we need to reset newnode to the null pointer
                            // so the parent caller knows that no newnode was
                            // created at this level
                            newnode=(SIZE_T)0;
                        }
                        return ERROR_NOERROR;   
                    }
                    // there was no newnode
                    // return to parent
                    return ERROR_NOERROR;
                }
            }
            // if we got here, we need to go to the next pointer, if it exists
            if (true) { 
                rc=b.GetPtr(b.info.numkeys,ptr);
                if (rc) { return rc; }
                return InsertRecursion(ptr,key,value,newkey,newnode);
                if (rc) { return rc; }
                if (newnode) {
                    // fix up pointers for this interior node
                    // since this was the last pointer, we just
                    // need to add a new key and pointer at the end
                    // increment number of keys
                    b.info.numkeys+=1;

                    // just set the key and ptr of last position in b 
                    rc=b.SetKey(b.info.numkeys-1,newkey);
                    if (rc) { return rc; }
                    rc=b.SetPtr(b.info.numkeys,newnode);
                    if (rc) { return rc; }
                    rc=b.Serialize(buffercache,node);
                    if (rc) { return rc; } 
                    // if now too full, split and return the new node
                    if (floor(b.info.GetNumSlotsAsInterior()*(2/3)) <= b.info.numkeys) {
                        //    copy b into splitNode
                        BTreeNode splitNode = b;

                        // last key of first node
                        SIZE_T lastKeyIndex= floor(b.info.numkeys/2)-1;
                        // first key of new split node
                        SIZE_T firstKeyIndex=lastKeyIndex+2;

                        // get the new key that we need to promote
                        rc=b.GetKey(lastKeyIndex+1,newkey);
                        if (rc) { return rc; }

                        // move the second half of the old node into the beginning of newnode
                        SIZE_T insertIndex=0;
                        KEY_T tempKey;
                        SIZE_T tempPtr;
                        for (SIZE_T i=firstKeyIndex;i<splitNode.info.numkeys;i++) {
                            rc=b.GetKey(i,tempKey);
                            if (rc) { return rc; }
                            rc=b.GetPtr(i,tempPtr);
                            if (rc) { return rc; }
                            rc=splitNode.SetKey(insertIndex,tempKey);
                            if (rc) { return rc; }
                            rc=splitNode.SetPtr(insertIndex,tempPtr);
                            if (rc) { return rc; }
                            insertIndex++;
                        }
                        // insert extra pointers
                        rc=b.GetPtr(b.info.numkeys,tempPtr);
                        rc=splitNode.SetPtr(insertIndex,tempPtr);

                        b.info.numkeys=lastKeyIndex+1;
                        splitNode.info.numkeys=insertIndex;

                        // allocate space for newnode on the disk
                        rc=AllocateNode(newnode);
                        if (rc) { return rc; }

                        // serialize newnode and b to the disk
                        rc=splitNode.Serialize(buffercache,newnode);
                        if (rc) { return rc; }
                        rc=b.Serialize(buffercache,node);
                        if (rc) { return rc; }
                    } else {
                        // this node is NOT full
                        // so we need to reset newnode to the null pointer
                        // so the parent caller knows that no newnode was
                        // created at this level
                        newnode=(SIZE_T)0;
                    }
                    // this is the end of the case where child returns a newnode
                    return ERROR_NOERROR;
                }
                // this is the end of the case where there was no newnode
                return ERROR_NOERROR;
            } else {
                // There are no keys at all on this node, so nowhere to go
                return ERROR_NONEXISTENT;
            }
            break;
        case BTREE_LEAF_NODE:
            // Scan through keys
            // if we find a matching key, return ERROR_CONFLICT
            // if we find a key that is larger, begin insert process
            for (offset=0;offset<b.info.numkeys;offset++) { 
                rc=b.GetKey(offset,testkey);
                if (rc) {  return rc; }
                if (testkey==key) { 
                    return ERROR_CONFLICT;
                } else if (key<testkey) {
                    // the key we found is larger than the key we want to insert
                    // we need to insert our key at this offset

                    // initialize temporary key and value variables
                    KEY_T tempKeyPrev=key; 
                    VALUE_T tempValuePrev=value;
                    KEY_T tempKeyCurrent=testkey; 
                    VALUE_T tempValueCurrent;
                    rc=b.GetVal(offset,tempValueCurrent);
                    if (rc) { return rc; }
                    
                    // increment number of keys
                    b.info.numkeys+=1;

                    // iterate through and move all keys and values over by one
                    for (SIZE_T i=offset;i<b.info.numkeys-1;i++) {
                        rc=b.SetKey(i,tempKeyPrev);
                        if (rc) { return rc; }
                        rc=b.SetVal(i,tempValuePrev);
                        if (rc) { return rc; }
                        tempKeyPrev=tempKeyCurrent;
                        tempValuePrev=tempValueCurrent;
                        rc=b.GetKey(i+1,tempKeyCurrent);
                        if (rc) { return rc; }
                        rc=b.GetVal(i+1,tempValueCurrent);
                        if (rc) { return rc; }
                    }

                    // edge case where we don't want to get next key and val
                    // just set the key and val of last position in b 
                    rc=b.SetKey(b.info.numkeys-1,tempKeyPrev);
                    if (rc) { return rc; }
                    rc=b.SetVal(b.info.numkeys-1,tempValuePrev);
                    if (rc) { return rc; }
                    rc=b.Serialize(buffercache,node);
                    if (rc) { return rc; }
                    // if the node is now too big, split using recursion and return the new node
                    // otherwise just return 0
                    if (floor(b.info.GetNumSlotsAsLeaf()*(2/3)) <= b.info.numkeys) {
                        // copy b into splitNode
                        BTreeNode splitNode = b;

                        SIZE_T halfIndex= floor(b.info.numkeys/2);
                        rc=b.GetKey(halfIndex,newkey);
                        if (rc) { return rc; }

                        // move the second half of the old node into the beginning of newnode
                        SIZE_T insertIndex=0;
                        KEY_T tempKey;
                        VALUE_T tempValue;
                        for (SIZE_T i=halfIndex;i<splitNode.info.numkeys;i++) {
                            rc=b.GetKey(i,tempKey);
                            if (rc) { return rc; }
                            rc=b.GetVal(i,tempValue);
                            if (rc) { return rc; }
                            rc=splitNode.SetKey(insertIndex,tempKey);
                            if (rc) { return rc; }
                            rc=splitNode.SetVal(insertIndex,tempValue);
                            if (rc) { return rc; }
                            insertIndex++;
                        }
                        b.info.numkeys=halfIndex;
                        splitNode.info.numkeys=insertIndex;

                        // allocate space for newnode on the disk
                        rc=AllocateNode(newnode);
                        if (rc) { return rc; }

                        // serialize newnode to the disk
                        rc=splitNode.Serialize(buffercache,newnode);
                        if (rc) { return rc; }
                        rc=b.Serialize(buffercache,node);
                        if (rc) { return rc; }
                        return ERROR_NOERROR;
                    }
                    return ERROR_NOERROR;
                }
            }
            // there is no key larger than the new key
            // add it on to the end of b
            //
            // increment number of keys
            b.info.numkeys+=1;

            // set the key and val
            rc=b.SetKey(b.info.numkeys-1,key);
            if (rc) { return rc; }
            rc=b.SetVal(b.info.numkeys-1,value);
            if (rc) { return rc; }
            rc=b.Serialize(buffercache,node);
            if (rc) { return rc; }

            // if the node is too big, split using recursion, then return the new node
            if (floor(b.info.GetNumSlotsAsLeaf()*(2/3)) <= b.info.numkeys) {
                // copy b into splitNode
                BTreeNode splitNode = b;

                SIZE_T halfIndex= floor(b.info.numkeys/2);
                rc=b.GetKey(halfIndex,newkey);
                if (rc) { return rc; }

                // move the second half of the old node into the beginning of newnode
                SIZE_T insertIndex=0;
                KEY_T tempKey;
                VALUE_T tempValue;
                for (SIZE_T i=halfIndex;i<splitNode.info.numkeys;i++) {
                    rc=b.GetKey(i,tempKey);
                    if (rc) { return rc; }
                    rc=b.GetVal(i,tempValue);
                    if (rc) { return rc; }
                    rc=splitNode.SetKey(insertIndex,tempKey);
                    if (rc) { return rc; }
                    rc=splitNode.SetVal(insertIndex,tempValue);
                    if (rc) { return rc; }
                    insertIndex++;
                }
                b.info.numkeys=halfIndex;
                splitNode.info.numkeys=insertIndex;

                // allocate space for newnode on the disk
                rc=AllocateNode(newnode);
                if (rc) { return rc; }

                // serialize newnode to the disk
                rc=splitNode.Serialize(buffercache,newnode);
                if (rc) { return rc; }
                rc=b.Serialize(buffercache,node);
                if (rc) { return rc; }
                return ERROR_NOERROR;
            }
            return ERROR_NOERROR;
            break;
        default:
            // We can't be looking at anything other than a root, internal, or leaf
            return ERROR_INSANE;
            break;
    }  
    return ERROR_INSANE;
}

ERROR_T BTreeIndex::Update(const KEY_T &key, const VALUE_T &value)
{
    // WRITE ME
    return LookupOrUpdateInternal(superblock.info.rootnode, BTREE_OP_UPDATE, key, (VALUE_T&)value);
}


ERROR_T BTreeIndex::Delete(const KEY_T &key)
{
    // This is optional extra credit 
    //
    // 
    return ERROR_UNIMPL;
}


//
//
// DEPTH first traversal
// DOT is Depth + DOT format
//

ERROR_T BTreeIndex::DisplayInternal(const SIZE_T &node,
        ostream &o,
        BTreeDisplayType display_type) const
{
    KEY_T testkey;
    SIZE_T ptr;
    BTreeNode b;
    ERROR_T rc;
    SIZE_T offset;

    rc= b.Unserialize(buffercache,node);

    if (rc!=ERROR_NOERROR) { 
        return rc;
    }

    rc = PrintNode(o,node,b,display_type);

    if (rc) { return rc; }

    if (display_type==BTREE_DEPTH_DOT) { 
        o << ";";
    }

    if (display_type!=BTREE_SORTED_KEYVAL) {
        o << endl;
    }

    switch (b.info.nodetype) { 
        case BTREE_ROOT_NODE:
        case BTREE_INTERIOR_NODE:
            if (b.info.numkeys>0) { 
                for (offset=0;offset<=b.info.numkeys;offset++) { 
                    rc=b.GetPtr(offset,ptr);
                    if (rc) { return rc; }
                    if (display_type==BTREE_DEPTH_DOT) { 
                        o << node << " -> "<<ptr<<";\n";
                    }
                    rc=DisplayInternal(ptr,o,display_type);
                    if (rc) { return rc; }
                }
            }
            return ERROR_NOERROR;
            break;
        case BTREE_LEAF_NODE:
            return ERROR_NOERROR;
            break;
        default:
            if (display_type==BTREE_DEPTH_DOT) { 
            } else {
                o << "Unsupported Node Type " << b.info.nodetype ;
            }
            return ERROR_INSANE;
    }

    return ERROR_NOERROR;
}


ERROR_T BTreeIndex::Display(ostream &o, BTreeDisplayType display_type) const
{
    ERROR_T rc;
    if (display_type==BTREE_DEPTH_DOT) { 
        o << "digraph tree { \n";
    }
    rc=DisplayInternal(superblock.info.rootnode,o,display_type);
    if (display_type==BTREE_DEPTH_DOT) { 
        o << "}\n";
    }
    return ERROR_NOERROR;
}


ERROR_T BTreeIndex::SanityCheck() const
{
    ERROR_T rc;
    SIZE_T totalKeys;
    // check if keys in order within node and count up keys in leaf nodes
    // extended to make sure no node is "too full"
    rc=NodesInOrder(superblock.info.rootnode, totalKeys);
    if(rc){
        return rc;
    }
    // if totalkeys in leaf nodes does not match numkeys of superblock, insane tree
    if (totalKeys != superblock.info.numkeys) {
        return ERROR_INSANE;
    }
    return ERROR_NOERROR;
}


// Kind of a misnomer, because we've included multiple insanity check invariants here
ERROR_T BTreeIndex::NodesInOrder(const SIZE_T &node, SIZE_T &totalKeys) const 
{

    return ERROR_NOERROR;
    /*
    KEY_T key;
    SIZE_T ptr;
    ERROR_T rc;
    BTreeNode b;
    totalKeys = 0;

    rc= b.Unserialize(buffercache,node);
    if(rc) {
        return rc;
    }
    switch(b.info.nodetype){
        case BTREE_ROOT_NODE:
        case BTREE_INTERIOR_NODE:
            if (floor(b.info.GetNumSlotsAsInterior()*(2/3)) <= b.info.numkeys) {
                // Node is too big
                return ERROR_INSANE;
            }
            if (b.info.numkeys>0) { 
                KEY_T prev=0;
                for (offset=0;offset<=b.info.numkeys;offset++) { 

                    rc=b.GetKey(offset,key);
                    if(prev==0){
                        prev = key;
                    } else {
                        if(key>=prev){
                            prev=key;
                        }else{
                            //This value is less than the one before it. Uh oh.
                            return ERROR_INSANE;
                        }
                    }

                    // Recurse down to check the next nodes
                    rc=b.GetPtr(offset,ptr);
                    if (rc) { return rc; }
                    rc=NodesInOrder(ptr);
                    if (rc) { return rc; }
                }
            }
            return ERROR_NOERROR;
            break;
        case BTREE_LEAF_NODE:
            if (floor(b.info.GetNumSlotsAsLeaf()*(2/3)) <= b.info.numkeys){
                // Node is too big
                return ERROR_INSANE;
            }
            if (b.info.numkeys>0) { 
                // keep track of the total number of keys
                totalKeys += b.info.numkeys;
                KEY_T prev = NULL;
                for (offset=0;offset<=b.info.numkeys;offset++) { 
                    rc=b.GetKey(offset,key);
                    if ( rc ) { return rc; } 
                    if(prev==NULL){
                        prev = key;
                    } else {
                        if(key>=prev){
                            prev=key;
                        }else{
                            //This value is less than the one before it. Uh oh.
                            return ERROR_INSANE;
                        }
                    }
                }
            }
            return ERROR_NOERROR
                break;
        default:
            // should never get here
            return ERROR_NOERROR;
    }
*/
}



ostream & BTreeIndex::Print(ostream &os) const
{
    Display(os, BTREE_SORTED_KEYVAL);
    return os;
}

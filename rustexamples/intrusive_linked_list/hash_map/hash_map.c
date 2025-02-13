#include<stdlib.h>

#define DEFAULT_HASH_MAP_LENGTH 10

// maybe just use void* instead of List*
typedef struct List List;

extern List* empty_list();
extern List* find(List* l, int k);
extern List* insert(List* l, int k, int v);
extern List* remove(List* l, int k);
extern int delete_list(List* l);

// The hash function can be implemented in assembly. It must guarantee
// that the return index must less than DEFAULT_HASH_MAP_LENGTH.
extern int hash(int k, uint32_t range);

// We can also introduce handles to use multiple hash maps
static List* hmap[DEFAULT_HASH_MAP_LENGTH] = {NULL};

// Less efficient
void init_map(){
    for(int i = 0; i < DEFAULT_HASH_MAP_LENGTH; ++i){
        hmap[i] = empty_list();
    }
}

List** find_bucket(int key){
    int index = hash(key, DEFAULT_HASH_MAP_LENGTH);
    return &(hmap[index]);
}

void hmap_set(int key, int val){
    List** buk = find_bucket(key);
    if(*buk == NULL){
        List* list = empty_list(); // do we need to check the malloc result?
        list = insert(list, key, val);
        *buk = list;
    }
    else{
        *buk = insert(*buk, key, val);
    }

    // int index = hash(key);
    // if(hmap[index] == NULL){
    //     List* list = empty_list(); // do we need to check the malloc result?
    //     list = insert(list, key, val);
    //     hmap[index] = list;
    // }
    // else{
    //     hmap[index] = insert(hmap[index], key, val);
    // }
}

int process(int val){
    printf("The key is mapped to %d\n", val);
    return val;
}

// process_with_key takes (key, val) as arguments
int process_with_key(int key, int val){
    printf("The key %d is mapped to %d\n", key, val);
    return val;
}

void hmap_get(int key){
    List** buk = find_bucket(key);
    if(*buk == NULL){
        return;
    }
    else{
        find(*buk, key);
    }

    // int index = hash(key);
    // if(hmap[index] == NULL){
    //     return;
    // }
    // else{
    //     find(hmap[index], key);
    // }
}

void hmap_remove(int key){
    List** buk = find_bucket(key);
    if(*buk == NULL){
        return;
    }
    else{
        remove(*buk, key);
    }

    // int index = hash(key);
    // if(hmap[index] == NULL){
    //     return;
    // }
    // else{
    //     remove(hmap[index], key);
    // }
}

void delete_hmap(){
    for(int i = 0; i < DEFAULT_HASH_MAP_LENGTH; ++i){
        if (hmap[i] != NULL) delete_list(hmap[i]);
    }
    printf("Delete the hash map\n");
}

int main(){
    hmap_set(19, 10);
    hmap_get(19);
    delete_hmap();
}
#include<stdlib.h>
#include<stdio.h>

#define DEFAULT_HASH_MAP_LENGTH 10

typedef void* List_ptr; // bucket
typedef List_ptr* HashMap;
extern List_ptr empty_list(void);
extern List_ptr find_and_process(List_ptr l, int k);
extern List_ptr insert(List_ptr l, int k, int* v);
extern List_ptr list_remove(List_ptr l, int k);
extern int delete_list(List_ptr l);

// The hash function can be implemented in assembly. It must guarantee
// that the return index must less than DEFAULT_HASH_MAP_LENGTH.
extern unsigned int hash(int k, unsigned int range);

// We can also introduce handles to use multiple hash maps
// static List* hmap[DEFAULT_HASH_MAP_LENGTH] = {NULL};

// Less efficient
HashMap init_hmap(){
    HashMap hmap = malloc(sizeof(List_ptr) * DEFAULT_HASH_MAP_LENGTH);
    for(int i = 0; i < DEFAULT_HASH_MAP_LENGTH; ++i){
        // hmap[i] = empty_list();
        hmap[i] = NULL;
    }
    return hmap;
}

List_ptr* find_bucket(HashMap hmap, int key){
    unsigned int index = hash(key, DEFAULT_HASH_MAP_LENGTH);
    return &(hmap[index]);
}

void hmap_set(HashMap hmap, int key, int* val){
    List_ptr* buk = find_bucket(hmap, key);
    if(*buk == NULL){
        List_ptr l = empty_list(); // do we need to check the malloc result?
        l = insert(l, key, val);
        *buk = l;
    }
    else{
        *buk = insert(*buk, key, val);
    }
}

int process(int val){
    printf("The key is mapped to %d\n", val);
    return val;
}

int* process_box(int* val){
    printf("The key is mapped to a pointer points to %d\n", *val);
    return val;
}

// process_with_key takes (key, val) as arguments
int process_with_key(int key, int val){
    printf("The key %d is mapped to %d\n", key, val);
    return val;
}

void hmap_process(HashMap hmap, int key){
    List_ptr* buk = find_bucket(hmap, key);
    if(*buk == NULL){
        return;
    }
    else{
        *buk = find_and_process(*buk, key);
    }

    // int index = hash(key);
    // if(hmap[index] == NULL){
    //     return;
    // }
    // else{
    //     find(hmap[index], key);
    // }
}

void hmap_remove(HashMap hmap, int key){
    List_ptr* buk = find_bucket(hmap, key);
    if(*buk == NULL){
        return;
    }
    else{
        *buk = list_remove(*buk, key);
    }

    // int index = hash(key);
    // if(hmap[index] == NULL){
    //     return;
    // }
    // else{
    //     list_remove(hmap[index], key);
    // }
}

void delete_hmap(HashMap hmap){
    for(int i = 0; i < DEFAULT_HASH_MAP_LENGTH; ++i){
        if (hmap[i] != NULL) delete_list(hmap[i]);
    }
    free(hmap);
    printf("Deleted the hash map\n");
}

int main(){
    HashMap hmap = init_hmap();
    int *v1 = malloc(sizeof(int));
    *v1 = 10;
    int *v2 = malloc(sizeof(int));
    *v2 = 20;
    int *v3 = malloc(sizeof(int));
    *v3 = 30;
    hmap_set(hmap, 19, v1);
    hmap_set(hmap, 13, v2);
    hmap_set(hmap, 23, v3);
    hmap_process(hmap, 19);
    hmap_process(hmap, 13);
    hmap_process(hmap, 23);
    delete_hmap(hmap);
}
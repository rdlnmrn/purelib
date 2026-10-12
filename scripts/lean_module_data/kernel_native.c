/* Private pinned-ABI prototype. All kernel/metadata objects come from original
   official factories; no record construction, retagging or pointer casts. */
#define _POSIX_C_SOURCE 200809L
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void lean_initialize(void);
extern lean_object *lean_mk_empty_environment(uint32_t);
extern lean_object *lean_elab_environment_to_kernel_env(lean_object *);
extern lean_object *l_Lean_readModuleData(lean_object *);
extern lean_object *l_Lean_readModuleDataParts(lean_object *);
extern lean_object *lean_options_get_empty(lean_object *);
extern lean_object *l_Lean_NameMap_instEmptyCollection(lean_object *);
extern lean_object *l_Lean_importModules(lean_object *, lean_object *, uint32_t,
                                      lean_object *, uint8_t, uint8_t, uint8_t, lean_object *);
extern lean_object *lean_environment_find(lean_object *, lean_object *);
extern lean_object *l_Lean_initSearchPath(lean_object *, lean_object *);
extern lean_object *lean_add_decl(lean_object *, size_t, lean_object *, lean_object *);
extern lean_object *l_Lean_Kernel_Exception_toMessageData(lean_object *, lean_object *);
extern lean_object *l_Lean_MessageData_toString(lean_object *);
extern uint8_t l_Lean_Name_quickCmpAux(lean_object *, lean_object *);
/* Source declaration has the erased World slot; the installed generated Lean
   caller supplies only the two borrowed data arguments because World is unused. */
extern lean_object *lean_compacted_region_read(lean_object *, lean_object *, lean_object *);
extern lean_object *lean_compacted_region_free(lean_object *, lean_object *);
extern lean_object *lean_mk_inductive_decl(lean_object *,lean_object *,lean_object *,uint8_t);
extern uint8_t l_Lean_instBEqConstructorVal_beq(lean_object *,lean_object *);
extern uint8_t l_Lean_instBEqRecursorVal_beq(lean_object *,lean_object *);
extern uint8_t l_Lean_instBEqConstantVal_beq(lean_object *,lean_object *);
extern lean_object *lean_level_mk_param(lean_object *);
extern lean_object *lean_expr_mk_const(lean_object *,lean_object *);
static int shape(lean_object *,unsigned,unsigned);
static int name_lists_equal(lean_object *a,lean_object *b) {
    while(!lean_is_scalar(a)&&!lean_is_scalar(b)) {
        if(!shape(a,1,2)||!shape(b,1,2))exit(2);
        if(!lean_name_eq(lean_ctor_get(a,0),lean_ctor_get(b,0)))return 0;
        a=lean_ctor_get(a,1);b=lean_ctor_get(b,1);
    }
    return lean_is_scalar(a)&&lean_is_scalar(b)&&lean_unbox(a)==0&&lean_unbox(b)==0;
}

static int shape(lean_object *p, unsigned tag, unsigned fields) {
    return !lean_is_scalar(p) && lean_is_ctor(p) && lean_obj_tag(p) == tag && lean_ctor_num_objs(p) == fields;
}
static lean_object *retain(lean_object *p) { lean_inc(p); return p; }
static lean_object *take_io(lean_object *r) {
    if (!shape(r, 0, 1) && !shape(r, 1, 1)) { fputs("invalid official IO result\n", stderr); exit(2); }
    if (lean_io_result_is_error(r)) { lean_io_result_show_error(r); lean_dec(r); return NULL; }
    return lean_io_result_take_value(r);
}
static void release_regions(lean_object *holder) {
    lean_object *regions=lean_mk_empty_array();
    if (lean_is_array(holder)) {
        for(size_t i=0;i<lean_array_size(holder);i++) {
            lean_object *pair=lean_array_get_core(holder,i);
            if(!shape(pair,0,2))exit(2);
            regions=lean_array_push(regions,retain(lean_ctor_get(pair,1)));
        }
    } else {
        if(!shape(holder,0,2))exit(2);
        regions=lean_array_push(regions,retain(lean_ctor_get(holder,1)));
    }
    /* All root, declaration and environment uses must be gone before here.
       Region owners are real official records; original free clears their root. */
    lean_dec(holder);
    for(size_t i=lean_array_size(regions);i>0;i--) {
        lean_object *unit=take_io(lean_compacted_region_free(
            retain(lean_array_get_core(regions,i-1)),lean_box(0)));
        if(!unit)exit(2);lean_dec(unit);
    }
    lean_dec(regions);
}
/* Version-one counted transport. No data are encoded as command lines. */
extern lean_object *lean_io_error_to_string(lean_object *);
static lean_object *service_error=NULL;
static lean_object *service_io(lean_object *r) {
    if(!shape(r,0,1)&&!shape(r,1,1))exit(2);
    if(lean_io_result_is_error(r)) {
        service_error=lean_io_error_to_string(retain(lean_io_result_get_error(r)));
        lean_dec(r);return NULL;
    }
    return lean_io_result_take_value(r);
}
static void send_frame(uint8_t tag,const void *data,size_t size) {
    uint8_t header[9];header[0]=tag;
    for(unsigned i=0;i<8;i++)header[i+1]=(uint8_t)(((uint64_t)size)>>(8*i));
    if(fwrite(header,1,9,stdout)!=9||(size&&fwrite(data,1,size,stdout)!=size)||fflush(stdout))exit(2);
}
static void send_string(uint8_t tag,lean_object *text) {
    if(!lean_is_string(text))exit(2);
    send_frame(tag,lean_string_cstr(text),lean_string_size(text)-1);
}
static void send_io_error(void) {
    if(!service_error)exit(2);send_string(1,service_error);lean_dec(service_error);service_error=NULL;
}
static uint64_t read64(const uint8_t *p) {
    uint64_t n=0;for(unsigned i=0;i<8;i++)n|=((uint64_t)p[i])<<(8*i);return n;
}
static void send64(uint64_t n) {
    uint8_t b[8];for(unsigned i=0;i<8;i++)b[i]=(uint8_t)(n>>(8*i));send_frame(0,b,8);
}
static void send_comparison_error(const char *prefix,const uint8_t *name,size_t len,const char *tail) {
    char *buf=NULL;size_t size=0;FILE *f=open_memstream(&buf,&size);if(!f)exit(2);
    fputs(prefix,f);if(len)fwrite(name,1,len,f);fputs(tail,f);if(fclose(f))exit(2);
    send_frame(1,buf,size);free(buf);
}
static lean_object *service_load(const char *file,lean_object **roots) {
    lean_object *path=lean_mk_string(file),*pair=service_io(l_Lean_readModuleData(path));lean_dec(path);
    if(!pair)return NULL;
    if(!shape(pair,0,2)||!shape(lean_ctor_get(pair,0),0,5))exit(2);
    lean_object *data=lean_ctor_get(pair,0);
    if(!lean_ctor_get_uint8(data,5*sizeof(void*))) {*roots=pair;return retain(data);}
    release_regions(pair);const char *suffix[3]={"",".server",".private"};lean_object *paths=lean_mk_empty_array();
    for(unsigned i=0;i<3;i++) {
        size_t n=strlen(file)+strlen(suffix[i])+1;char *s=malloc(n);if(!s)exit(2);
        snprintf(s,n,"%s%s",file,suffix[i]);paths=lean_array_push(paths,lean_mk_string(s));free(s);
    }
    lean_object *parts=service_io(l_Lean_readModuleDataParts(paths));lean_dec(paths);
    if(!parts)return NULL;
    if(!lean_is_array(parts)||lean_array_size(parts)!=3)exit(2);
    pair=lean_array_get_core(parts,2);if(!shape(pair,0,2)||!shape(lean_ctor_get(pair,0),0,5))exit(2);
    *roots=parts;return retain(lean_ctor_get(pair,0));
}
static lean_object *service_add(lean_object *env,lean_object *decl,int replay,int probe,const uint8_t *name,size_t len) {
    if(replay&&shape(decl,2,1)) {
        lean_object *val=lean_ctor_get(decl,0),*base=lean_ctor_get(val,0);
        lean_object *found=lean_environment_find(retain(env),retain(lean_ctor_get(base,0)));
        int same=shape(found,1,1)&&shape(lean_ctor_get(found,0),2,1);
        if(same) {
            lean_object *current=lean_ctor_get(lean_ctor_get(found,0),0);
            same=l_Lean_instBEqConstantVal_beq(base,lean_ctor_get(current,0))&&name_lists_equal(lean_ctor_get(val,2),lean_ctor_get(current,2));
        }
        lean_dec(found);if(same){send_frame(0,NULL,0);return env;}
    }
    if(probe) {
        lean_object *val=lean_ctor_get(decl,0),*body=lean_ctor_get(val,1);
        if(!shape(body,4,2))exit(2);
        lean_object *levels=lean_ctor_get(body,1),*cursor=levels;
        while(!lean_is_scalar(cursor)) {
            if(!shape(cursor,1,2))exit(2);
            lean_object *level=lean_ctor_get(cursor,0);if(!shape(level,4,1))exit(2);
            lean_object *reference=lean_level_mk_param(retain(lean_ctor_get(level,0)));
            if(!shape(reference,4,1)||lean_ctor_get_uint64(level,sizeof(void*))!=lean_ctor_get_uint64(reference,sizeof(void*))) {
                fputs("prototype Level.param cache mismatch\n",stderr);exit(2);
            }
            lean_dec(reference);cursor=lean_ctor_get(cursor,1);
        }
        if(lean_unbox(cursor)!=0)exit(2);
        lean_object *reference=lean_expr_mk_const(retain(lean_ctor_get(body,0)),retain(levels));
        if(!shape(reference,4,2)||lean_ctor_get_uint64(body,2*sizeof(void*))!=lean_ctor_get_uint64(reference,2*sizeof(void*))) {
            fputs("prototype Expr.const cache mismatch\n",stderr);exit(2);
        }
        lean_dec(reference);
    }
    lean_object *r=lean_add_decl(probe?retain(env):env,0,decl,lean_box(0));
    if(!shape(r,0,1)&&!shape(r,1,1))exit(2);
    if(lean_obj_tag(r)==0) {
        lean_object *text=l_Lean_MessageData_toString(l_Lean_Kernel_Exception_toMessageData(retain(lean_ctor_get(r,0)),lean_options_get_empty(lean_box(0))));lean_dec(r);
        if(!lean_is_string(text))exit(2);
        char *buf=NULL;size_t size=0;FILE *f=open_memstream(&buf,&size);if(!f)exit(2);
        fputs(replay?"while replaying declaration '":"kernel rejected ",f);fwrite(name,1,len,f);fputs(replay?"':\n":": ",f);
        fwrite(lean_string_cstr(text),1,lean_string_size(text)-1,f);if(fclose(f))exit(2);
        send_frame(1,buf,size);free(buf);lean_dec(text);if(probe)lean_dec(env);return NULL;
    }
    lean_object *next=retain(lean_ctor_get(r,0));lean_dec(r);
    if(probe){lean_dec(next);next=env;}
    send_frame(0,NULL,0);return next;
}
/* Each exported constructor consumes exactly the owned arguments supplied here. */
extern lean_object *lean_expr_mk_bvar(lean_object *);
extern lean_object *lean_expr_mk_fvar(lean_object *);
extern lean_object *lean_expr_mk_mvar(lean_object *);
extern lean_object *lean_expr_mk_sort(lean_object *);
extern lean_object *lean_expr_mk_app(lean_object *,lean_object *);
extern lean_object *lean_expr_mk_lambda(lean_object *,lean_object *,lean_object *,uint8_t);
extern lean_object *lean_expr_mk_forall(lean_object *,lean_object *,lean_object *,uint8_t);
extern lean_object *lean_expr_mk_let(lean_object *,lean_object *,lean_object *,lean_object *,uint8_t);
extern lean_object *lean_expr_mk_lit(lean_object *);
extern lean_object *lean_expr_mk_mdata(lean_object *,lean_object *);
extern lean_object *lean_expr_mk_proj(lean_object *,lean_object *,lean_object *);
static int service_cache(const char *file) {
    lean_object *deps=lean_mk_empty_array(),*path=lean_mk_string(file);
    lean_object *holder=service_io(lean_compacted_region_read(path,deps,lean_box(0)));lean_dec(deps);lean_dec(path);
    if(!holder)return 1;
    lean_object *values=lean_ctor_get(holder,0);if(!lean_is_array(values))return 2;
    
    for(size_t i=0;i<lean_array_size(values);i++) {
        lean_object *e=lean_array_get_core(values,i),*r=NULL;
        if(lean_is_scalar(e)||!lean_is_ctor(e))return 2;
        unsigned tag=lean_obj_tag(e),count=lean_ctor_num_objs(e);
        uint8_t scalar=tag==6||tag==7||tag==8?lean_ctor_get_uint8(e,count*sizeof(void*)+8):0;
        #define F(n) retain(lean_ctor_get(e,n))
        switch(tag) {
        case 0:r=lean_expr_mk_bvar(F(0));break;
        case 1:r=lean_expr_mk_fvar(F(0));break;
        case 2:r=lean_expr_mk_mvar(F(0));break;
        case 3:r=lean_expr_mk_sort(F(0));break;
        case 4:r=lean_expr_mk_const(F(0),F(1));break;
        case 5:r=lean_expr_mk_app(F(0),F(1));break;
        case 6:r=lean_expr_mk_lambda(F(0),F(1),F(2),scalar);break;
        case 7:r=lean_expr_mk_forall(F(0),F(1),F(2),scalar);break;
        case 8:r=lean_expr_mk_let(F(0),F(1),F(2),F(3),scalar);break;
        case 9:r=lean_expr_mk_lit(F(0));break;
        case 10:r=lean_expr_mk_mdata(F(0),F(1));break;
        case 11:r=lean_expr_mk_proj(F(0),F(1),F(2));break;
        default:return 2;
        }
        #undef F
        if(!shape(r,tag,count)||lean_expr_data(e)!=lean_expr_data(r)) {
            fprintf(stderr,"complete Expr cache mismatch index %zu tag %u: %016llx != %016llx\n",i,tag,
                (unsigned long long)lean_expr_data(e),(unsigned long long)lean_expr_data(r));return 2;
        }
        for(unsigned j=0;j<count;j++)if(lean_ctor_get(e,j)!=lean_ctor_get(r,j))return 2;
        if((tag==6||tag==7||tag==8)&&scalar!=lean_ctor_get_uint8(r,count*sizeof(void*)+8))return 2;
        lean_dec(r);
    }
    send64(lean_array_size(values));
    release_regions(holder);return 0;
}

static int service(const char *old_file,const char *new_file,const char *sysroot) {
    lean_object *unit=service_io(l_Lean_initSearchPath(lean_mk_string(sysroot),lean_box(0)));
    if(!unit){send_io_error();return 1;}lean_dec(unit);
    lean_object *roots[2]={NULL,NULL},*data[2]={NULL,NULL},*env=NULL,*packets=lean_mk_empty_array();int result=0;
    for(unsigned i=0;i<2;i++) {data[i]=service_load(i?new_file:old_file,&roots[i]);if(!data[i]){send_io_error();result=1;goto finish;}}
    send_frame(0,NULL,0);
    for(;;) {
        uint8_t header[9];size_t got=fread(header,1,9,stdin);if(!got)break;if(got!=9){result=2;break;}
        uint64_t length=read64(header+1);if(length>SIZE_MAX-1){result=2;break;}
        uint8_t *payload=malloc((size_t)length+1);if(!payload){result=2;break;}
        if(length&&fread(payload,1,(size_t)length,stdin)!=length){free(payload);result=2;break;}payload[length]=0;
        uint8_t op=header[0];
        if(op==0) {free(payload);send_frame(0,NULL,0);break;}
        if(op==2) {
            if(length||env){free(payload);result=2;break;}
            lean_object *e=service_io(l_Lean_importModules(retain(lean_ctor_get(data[0],0)),lean_options_get_empty(lean_box(0)),0,lean_mk_empty_array(),0,0,2,l_Lean_NameMap_instEmptyCollection(lean_box(0))));
            if(!e){send_io_error();free(payload);result=1;break;}
            env=lean_elab_environment_to_kernel_env(e);send_frame(0,NULL,0);
        } else if(op==3) {
            if(memchr(payload,0,length)){free(payload);result=2;break;}
            lean_object *path=lean_mk_string((char*)payload),*deps=lean_mk_empty_array();
            lean_object *holder=service_io(lean_compacted_region_read(path,deps,lean_box(0)));lean_dec(path);lean_dec(deps);
            if(!holder){send_io_error();free(payload);result=1;break;}
            if(!shape(holder,0,2)){result=2;free(payload);break;}
            lean_object *packet=lean_ctor_get(holder,0);
            if(!lean_is_array(packet)||lean_array_size(packet)!=4){result=2;free(payload);release_regions(holder);break;}
            for(unsigned i=0;i<4;i++)if(!lean_is_array(lean_array_get_core(packet,i)))exit(2);
            uint64_t index=lean_array_size(packets);packets=lean_array_push(packets,holder);send64(index);
        } else if(op==8) {
            if(memchr(payload,0,length)){free(payload);result=2;break;}
            int code=service_cache((char*)payload);
            if(code){if(service_error)send_io_error();free(payload);result=code;break;}
        } else if(op==4) {
            if(!env||length!=16){result=2;free(payload);break;}
            uint64_t slot=read64(payload),index=read64(payload+8);if(slot>=lean_array_size(packets))exit(2);
            lean_object *holder=lean_array_get_core(packets,slot),*names=lean_array_get_core(lean_ctor_get(holder,0),1);
            if(index>=lean_array_size(names))exit(2);
            lean_object *found=lean_environment_find(retain(env),retain(lean_array_get_core(names,index)));
            uint8_t yes=shape(found,1,1);lean_dec(found);send_frame(0,&yes,1);
        } else if(op==5) {
            if(!env||length<24){result=2;free(payload);break;}
            uint64_t slot=read64(payload),index=read64(payload+8),mode=read64(payload+16);const uint8_t *name=payload+24;size_t len=(size_t)length-24;
            lean_object *values,*decl;
            if(slot<2)values=lean_ctor_get(data[slot],2);
            else {if(slot-2>=lean_array_size(packets))exit(2);lean_object *packet=lean_ctor_get(lean_array_get_core(packets,slot-2),0);values=lean_array_get_core(packet,mode==2?2:mode==3?3:0);}
            if(!lean_is_array(values)||index>=lean_array_size(values))exit(2);
            decl=lean_array_get_core(values,index);
            if(mode==2) {
                if(!shape(decl,0,2)||!shape(lean_ctor_get(decl,1),0,2))exit(2);
                lean_object *tail=lean_ctor_get(decl,1);decl=lean_mk_inductive_decl(retain(lean_ctor_get(decl,0)),retain(lean_ctor_get(tail,0)),retain(lean_ctor_get(tail,1)),0);
            } else if(mode==3) {if(!lean_is_scalar(decl)||lean_unbox(decl)!=4)exit(2);lean_inc(decl);}
            else {if(!lean_is_ctor(decl)||lean_obj_tag(decl)>3||lean_ctor_num_objs(decl)!=1)exit(2);lean_inc(decl);}
            env=service_add(env,decl,mode==0||mode==2||mode==3,mode==1,name,len);lean_dec(decl);
            if(!env){result=1;free(payload);break;}
        } else if(op==6||op==7) {
            if(!env||length<8){result=2;free(payload);break;}uint64_t index=read64(payload);unsigned tag=op==6?6:7;
            lean_object *infos=lean_ctor_get(data[0],2);if(index>=lean_array_size(infos))exit(2);
            lean_object *original=lean_array_get_core(infos,index);if(!shape(original,tag,1))exit(2);
            lean_object *val=lean_ctor_get(original,0),*base=lean_ctor_get(val,0);
            lean_object *found=lean_environment_find(retain(env),retain(lean_ctor_get(base,0)));
            const char *label=op==6?"constructor ":"recursor ";
            if(!shape(found,1,1)||!shape(lean_ctor_get(found,0),tag,1)){char prefix[40];snprintf(prefix,sizeof(prefix),"No such %s",label);send_comparison_error(prefix,payload+8,(size_t)length-8,"");}
            else {
                lean_object *current=lean_ctor_get(lean_ctor_get(found,0),0);
                uint8_t same=op==6?l_Lean_instBEqConstructorVal_beq(current,val):l_Lean_instBEqRecursorVal_beq(current,val);
                if(same)send_frame(0,NULL,0);
                else {char prefix[40];snprintf(prefix,sizeof(prefix),"Invalid %s",label);send_comparison_error(prefix,payload+8,(size_t)length-8,"");}
            }
            lean_dec(found);
        } else {result=2;free(payload);break;}
        free(payload);
    }
finish:
    if(env)lean_dec(env);
    for(size_t i=lean_array_size(packets);i>0;i--) {lean_object *h=retain(lean_array_get_core(packets,i-1));lean_array_set_core(packets,i-1,lean_box(0));lean_dec(h);release_regions(h);}
    lean_dec(packets);
    for(unsigned i=0;i<2;i++){if(data[i])lean_dec(data[i]);if(roots[i])release_regions(roots[i]);}
    return result;
}

int main(int argc,char **argv) {
    lean_initialize();lean_io_mark_end_initialization();
    if(argc==5&&strcmp(argv[1],"service")==0)return service(argv[2],argv[3],argv[4]);
    fputs("usage: service OLD_OLEAN NEW_OLEAN SYSROOT\n",stderr);return 2;
}

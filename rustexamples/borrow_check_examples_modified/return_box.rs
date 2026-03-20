fn retbox() -> Box<i32>{
    return Box::new(1);
}

fn t() -> bool{
    return false;
}

fn consume(x: Box<i32>){
    
}

fn main(){
    *retbox() = *retbox();
}
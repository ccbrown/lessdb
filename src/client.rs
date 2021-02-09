use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
pub struct Request<'a> {
    pub id: u64,

    #[serde(borrow)]
    pub body: RequestBody<'a>,
}

#[derive(Deserialize)]
pub enum RequestBody<'a> {
    Get { key: &'a [u8] },
    Set { key: &'a [u8], value: &'a [u8] },
}

#[derive(Serialize)]
pub struct Response<'a> {
    pub id: u64,

    pub body: ResponseBody<'a>,
}

#[derive(Serialize)]
pub enum ResponseBody<'a> {
    Error { code: String },
    GetResult { value: Option<&'a [u8]> },
}

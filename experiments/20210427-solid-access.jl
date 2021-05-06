# Based on
# https://gitlab.com/agentydragon/solid-flask/-/blob/master/solid_flask_main.py

# This implementation is not secure.
# Many required cryptographic checks were ignored.

using HTTP
using JSON
using Base64
using Random
using SHA
using Sockets
using PyCall
using Dates

const pyjwk = pyimport("jwcrypto.jwk")
const pyjwt = pyimport("jwcrypto.jwt")

const _ISSUER        = "https://inrupt.net/"
const _PORT          = 3333
const _REDIRECT_PATH = "/oauth/callback"
const _REDIRECT_URI  = "http://localhost:" * string(_PORT) * _REDIRECT_PATH
const _AUTHORITY     = _ISSUER * ".well-known/openid-configuration"

const random_device = RandomDevice()
const state_storage = Dict{String,Dict{String,String}}()
const access_token  = Ref("")
const key           = Ref("")

function register_client(provider_info)
    url     = provider_info["registration_endpoint"]
    headers = ["content-type" => "application/json"]
    data    = Dict("redirect_uris" => [_REDIRECT_URI])
    result  = JSON.parse(String(HTTP.post(url, headers, JSON.json(data)).body))
    @info "registration response" result
    return result["client_id"]
end

function make_random_string()
    randstring(random_device, 50)
end

function make_verifier_challenge()
    code_verifier  = make_random_string()
    code_challenge = base64encode(sha256(code_verifier))
    code_challenge = replace(replace(replace(code_challenge, "+" => "-"), "/" => "_"), "=" => "")
    code_verifier, code_challenge
end

const provider_info = JSON.parse(String(HTTP.request("GET", _AUTHORITY).body))
@info "provider info" provider_info

const client_id = register_client(provider_info)

function template(web_id, resource, resource_content)
    web_str = web_id != "" ? 
        "You are logged in as $(web_id)." : 
        "You are not logged in."
    res_str = resource != "" ? 
        "<pre>$(resource_content)</pre>" : 
        "Use the form below to read a resource."
    
    """
    <h2>Login status</h2>
    $(web_str)
    
    <h2>Resource content</h2>
    $(res_str)

    <form action=/ method=GET>
      <input
          value="$(resource)"
          placeholder='https://you.solidcommunity.net/private/...'
          name='resource'>
      <input type=submit value=Read>
    </form>
    """
end

function make_token_for(pykeypair, uri, method)
    header = Dict(
        "typ" => "dpop+jwt",
        "alg" => "ES256",
        "jwk" => pykeypair.export(private_key=false, as_dict=true)
    )
    claims = Dict(
        "jti" => make_random_string(),
        "htm" => method,
        "htu" => uri,
        "iat" => Int(floor(datetime2unix(now())))
    )
    jwt = pyjwt.JWT(header=header, claims=claims)
    jwt.make_signed_token(pykeypair)
    return jwt.serialize()
end

function index(req::HTTP.Request)
    queryparams = HTTP.queryparams(HTTP.URI(req.target))
    tested_url  = get(queryparams, "resource", "")

    if access_token[] != "" && key[] != ""
        println("loading access token and key from session")
        keypair = pyjwk.JWK.from_json(key[])
        headers = [
            "authorization" => "DPoP " * access_token[],
            "dpop"          => make_token_for(keypair, tested_url, "GET")
        ]
        decoded_access_token = pyjwt.JWT(jwt=access_token[])
        web_id = JSON.parse(decoded_access_token.token.objects["payload"])["sub"]
    else
        headers = Pair{String, String}[]
        web_id = ""
    end
    
    if tested_url != ""
        resp = HTTP.get(tested_url, headers; status_exception = false)
        if resp.status == 401
            println("Got 401 trying to access " * tested_url)
            code_verifier, code_challenge = make_verifier_challenge()
            state = make_random_string()
            @assert !haskey(state_storage,state)
            state_storage[state] = Dict("code_verifier" => code_verifier, "redirect_url" => req.target)
            
            url = provider_info["authorization_endpoint"] * "?" * HTTP.escapeuri([
                "code_challenge"        => code_challenge,
                "state"                 => state,
                "response_type"         => "code",
                "redirect_uri"          => _REDIRECT_URI,
                "code_challenge_method" => "S256",
                "client_id"             => client_id,
                "scope"                 => "openid offline_access"
            ])
            return HTTP.Response(302,["Location" => url])
        elseif resp.status != 200
            error("Unexpected status code: $(resp.status) $(resp.body)")
        end
        resource_content = String(resp.body)
    else
        resource_content = ""
    end
    headers = ["Content-Type" => "text/html"]
    return HTTP.Response(200, headers; body=template(web_id,tested_url,resource_content))
end

function oauth_callback(req::HTTP.Request)
    queryparams = HTTP.queryparams(HTTP.URI(req.target))
    auth_code   = get(queryparams, "code", "")
    state       = get(queryparams, "state", "")
    
    @assert haskey(state_storage, state) "state $(state) not in state_storage?"
    
    pykeypair     = pyjwk.JWK.generate(kty="EC", crv="P-256")
    key[]         = pykeypair.export()

    state_info    = state_storage[state]
    code_verifier = state_info["code_verifier"]
    redirect_url  = state_info["redirect_url"]
    
    url     = provider_info["token_endpoint"]
    headers = [
        "dpop" => make_token_for(pykeypair, url, "POST"),
        "content-type" => "application/x-www-form-urlencoded"
    ]
    data    = HTTP.escapeuri([
        "grant_type"    => "authorization_code",
        "client_id"     => client_id,
        "redirect_uri"  => _REDIRECT_URI,
        "code"          => auth_code,
        "code_verifier" => code_verifier
    ])
    result = JSON.parse(String(HTTP.post(url, headers, data; redirect=false).body))
    access_token[] = result["access_token"]

    pop!(state_storage, state)
    return HTTP.Response(302, ["Location" => redirect_url])
end

const ROUTER = HTTP.Router()
HTTP.@register(ROUTER, "GET", "/", index)
HTTP.@register(ROUTER, "GET", "/oauth/callback", oauth_callback)
@async HTTP.serve(ROUTER, ip"127.0.0.1", _PORT)



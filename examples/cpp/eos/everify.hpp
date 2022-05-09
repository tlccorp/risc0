#pragma once

#include <eosio/asset.hpp>
#include <eosio/eosio.hpp>
#include <eosio/time.hpp>
#include <eosio/print.hpp>
#include <eosio/system.hpp>
#include <eosio/crypto.hpp>
#include <string>
#include <eosio/multi_index.hpp>
#include <eosio/contract.hpp>

#include <string>

class [[eosio::contract]] everify : public eosio::contract
{
public:
	everify( eosio::name receiver, eosio::name code, eosio::datastream<const char*> ds ): eosio::contract( receiver, code, ds )
	{}
	
		struct [[eosio::table]] dwconfig {
		uint64_t id;
		eosio::name saname;
		eosio::name token_contract;
		std::string token_name;
		uint64_t primary_key() const
		{
			return id;
		}
		EOSLIB_SERIALIZE(dwconfig, (id)(saname)(token_contract)(token_name))
	};
	typedef eosio::multi_index<"dwconfig"_n, dwconfig> dwconfig_index;


	[[eosio::action]]
	void clean();
};

/*
 *@Date: 2022-01-05 10:19:23
 *@Description: 个人中心固定头部
 */
import {
  CommonUtils,
  componentautoscaling,
  RouterUtils,
  screenSize as getScreenSize,
  ScreenUtils,
  t,
  WithTheme,
  itemExposeHoc,
  monitor,
  EventTracking,
  Service as env,
  HttpService,
  PlatformUtils,
  DarkStore,
  RecordUtils,
} from '@hw-vmall/vrn-basic-comp';
import { SvgIcon, FastImageView, LoginWindow } from '@hw-vmall/vrn-bussiness-comp';
import React, { Component } from 'react';
import { Dimensions, Text, TouchableOpacity, View } from 'react-native';
import ImgArray from '../../../../../assets/ImgArray';
import Personal from '../personal-asster/indexWeb';
import dapReportList from './dapReportList';
import styles from './style/index';
const TAG = 'personal-user-info';
class UserInfo extends Component<any, any> {
  // 适配IOS每日签到重定向地址跳转
  eventListener: any;
  linkFinished: boolean;
  signUrl: string;
  constructor(props) {
    super(props);
    this.state = {
      showLoginWindow: false,
      showTopRightCorner: this.props.headStyle?.topRightCornerShow === '1',
      addressConfigKey: 'rn_web_ftl_address_rn',
    };
  }

  componentDidMount() {
    const { addressConfigKey } = this.state;
    if (this.isPc() && !sessionStorage.getItem(addressConfigKey)) {
      HttpService.querySystemConfig(addressConfigKey).then((res) => {
        const { systemConfigValue } = res.systemConfigInfos?.[addressConfigKey] || 0;
        sessionStorage.setItem(addressConfigKey, systemConfigValue);
      });
    }
  }

  componentDidUpdate() {}

  componentWillUnmount() {}

  isApp = () => {
    return (this.getSize() === 'small' || this.getSize() === 'medium') && !PlatformUtils.isWeb();
  };
  getSize = () => {
    return getScreenSize(this.props.width);
  };
  isPc = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return PlatformUtils.isPc(width);
  };
  // 屏幕尺寸大于1200，并为web平台下，渲染为pad样式
  isPadPc = () => {
    return this.getSize() === 'medium' && this.isPadHorizonta() && this.props.width >= 1024;
  };
  isPad = () => {
    return this.getSize() === 'medium';
  };

  isPadHorizonta = () => {
    return ScreenUtils.isPadHorizontal(
      CommonUtils.getWindowSize('personal').screenWidth,
      CommonUtils.getWindowSize('personal').screenHeight,
    );
  };

  // wap端拉起登录
  loginWeb(actionName) {
    const path: string = encodeURIComponent(window.location.href);
    const loginUrl = this.isPc()
      ? `${env.webDomain}account/login?url=${path}`
      : `${env.wapDomain}account/applogin?url=${path}`;
    this.props.clickItem(this.isPc() ? 310000101 : 210000101, loginUrl, actionName?.includes('昵称') ? 2 : 1);
    EventTracking.execReportData('', true);
    RouterUtils.gotoPage(loginUrl, false);
    // 没有登录 先跳转登录 后再跳客服页面 点击登录特殊处理
  }

  isApkOrIos = () => {
    return PlatformUtils.isApp();
  };

  isApkOrHap = () => {
    return PlatformUtils.isAndroid() || PlatformUtils.isHarmony();
  };

  isIos = () => {
    PlatformUtils.isIOS();
  };
  // 点击头像
  userInfoClick = (actionName?: any) => {
    let url;
    const isShow = this.isApkOrHap() ? 'APP' : 'IOS';
    const appCode = this.isApkOrIos() ? 110000101 : 210000101;
    if (this.isApkOrIos()) {
      url = `vmall://com.vmall.client/home/activity?pn=MemberPrivilege${isShow}&isShowLayout=false`;
    } else {
      url = this.isPc()
        ? `${env.upUserUrl}`
        : `${env.wapDomain}portal/activity/index.html?pn=MemberPrivilegeWAP&isShowLayout=false
        `;
    }
    if (this.props.isLogin) {
      this.props.clickItem(this.isPc() ? 310000101 : appCode, url, actionName?.includes('昵称') ? 2 : 1);
      EventTracking.execReportData('', true);
      if (this.props.enableAdvancedFeature === 0 && !PlatformUtils.isWeb()) {
        return;
      }
      RouterUtils.gotoPage(url);
    } else {
      // 未登录情况下拉起登录
      if (PlatformUtils.isWeb()) {
        this.loginWeb(actionName);
      } else {
        // apk拉起登录
        url = 'vmall://com.vmall.client/home/login';
        this.props.clickItem(this.isPc() ? 310000101 : appCode, url, actionName?.includes('昵称') ? 2 : 1);
        EventTracking.execReportData('', true);
        RouterUtils.gotoPage(url);
      }
    }
  };

  // 我的权益点击
  myPrivilegeClick = () => {
    let url;
    const isShow = this.isApkOrHap() ? 'APP' : 'IOS';
    if (this.isApkOrIos()) {
      url = `vmall://com.vmall.client/home/activity?pn=MemberPrivilege${isShow}&isShowLayout=false`;
    } else {
      url = this.isPc()
        ? `${env.webDomain}portal/activity/index.html?isShowLayout=false&pn=huiyuanPC`
        : `${env.wapDomain}portal/activity/index.html?pn=MemberPrivilegeWAP&isShowLayout=false`;
    }
    const appCode = this.isApkOrIos() ? 110000101 : 210000101;
    this.props.clickItem(this.isPc() ? 310000101 : appCode, url, 4);
    EventTracking.execReportData('', true);
    if (this.props.isLogin) {
      RouterUtils.gotoPage(url);
    } else {
      // 未登录情况下拉起登录
      if (PlatformUtils.isWeb()) {
        this.loginWeb(url);
      }
    }
  };
  // pc侧获取地址url
  getAddressUrlPc = () => {
    const configValue = Number(sessionStorage.getItem(this.state.addressConfigKey));
    return configValue === 1 ? `${env.webDomain}sc/address/index.html` : `${env.webDomain}member/myAddress`;
  };
  // 收货地址点击
  myAddressClick = () => {
    let url;
    if (this.isApkOrIos()) {
      url = 'vmall://com.vmall.client/address/index';
    } else {
      url = this.isPc() ? this.getAddressUrlPc() : `${env.wapDomain}address/manager`;
    }
    const appCode = this.isApkOrIos() ? 110000101 : 210000101;
    this.props.clickItem(this.isPc() ? 310000101 : appCode, url, 5);
    EventTracking.execReportData('', true);
    if (this.props.isLogin) {
      RouterUtils.gotoPage(url);
    } else {
      // 未登录情况下拉起登录
      if (PlatformUtils.isWeb()) {
        this.loginWeb(url);
      }
    }
  };
  // 每日签到点击 签到无了
  signClick = () => {
    const url = this.props.headStyle?.topRightCornerLink;
    const appCode = PlatformUtils.isApp() ? '110000101' : '210000101';
    this.props.clickItem(this.isPc() ? '310000101' : appCode, url, 6);
    EventTracking.execReportData('', true);
    RouterUtils.gotoPage(url);
  };
  // 关闭登录弹窗
  onClose = () => {
    this.setState({
      showLoginWindow: false,
    });
  };

  // 我的会员
  renderMyMember = (_styles: any, theme: any, useNewLayout: boolean) => {
    const { mergeStyle, width } = this.props;
    return (
      <>
        {useNewLayout ? (
          <TouchableOpacity
            activeOpacity={1}
            style={[_styles.tagText, this.getBgColorForUseLevel(mergeStyle)]}
            onPress={this.myPrivilegeClick}
          >
            <FastImageView localSource={ImgArray.medal} imgStyle={{ width: 14, height: 17 }} />
            <View style={_styles.txtBg}>
              <Text style={[_styles.tagTxt, this.getMergeStyle(mergeStyle)]}>
                V{this.props?.userLevel}
                {t('grade')}
              </Text>
            </View>
          </TouchableOpacity>
        ) : (
          <TouchableOpacity
            activeOpacity={1}
            style={[this.isPc() ? _styles.tagTextPc : _styles.tagText, this.getBgColorForUseLevel(mergeStyle)]}
            onPress={this.myPrivilegeClick}
          >
            <Text style={_styles.scaleWeb}>
              <Text style={[{ marginRight: 2 }, this.getMergeStyle(mergeStyle)]}>
                V{this.props?.userLevel}
                {t('grade')}
              </Text>
              {PlatformUtils.isWap(width) ? null : (
                <SvgIcon
                  viewBox={'-400 0 1024 1024'}
                  normalCol={this.getNormalCol(theme, mergeStyle)}
                  opacity={0.6}
                  iconName={'ic24-more'}
                  width={8}
                  height={16}
                />
              )}
            </Text>
          </TouchableOpacity>
        )}
      </>
    );
  };
  // 未登录
  notLogin = (_styles, mergeStyle) => {
    const textColor = mergeStyle?.textStyle?.color && !this.props.isMember ? mergeStyle?.textStyle : null;
    const unLoginText = PlatformUtils.isHarmony() ? t('harmonyLogin') : `${t('login')}/${t('register')}`;
    return (
      <>
        <TouchableOpacity
          style={_styles.noLogin}
          activeOpacity={1}
          onPress={() => {
            this.userInfoClick(t('click_nickname_to_grade_page'));
          }}
        >
          <Text style={[_styles.userName, this.isPc() ? null : textColor]}>{unLoginText}</Text>
        </TouchableOpacity>
        {/* web端未登录每日签到入口 */}
        {this.state.showTopRightCorner && this.isPc() && this.renderSignIn(_styles)}
      </>
    );
  };
  // 账户名
  accountName = (_styles, AccountName, mergeStyle) => {
    const isPc = this.isPc();
    return (
      <View style={isPc ? _styles.accountContentPc : _styles.accountContent}>
        <Text
          numberOfLines={1}
          ellipsizeMode={'tail'}
          textBreakStrategy={'simple'}
          style={[
            isPc ? _styles.userAccountPc : _styles.userAccount,
            mergeStyle?.textStyle?.color && !this.props.isMember ? mergeStyle?.textStyle : null,
          ]}
        >
          {`${t('AccountName')}${AccountName}`}
        </Text>
      </View>
    );
  };

  // 用户头像
  userHeadImg = (_styles, showText, showIcon, item, avatarIcon) => {
    const titleMarginLeft = showIcon ? -2 : 0;
    // 登录状态下默认头像
    const loginDefaultAvatar = PlatformUtils.isHarmony() ? ImgArray.harmonyloginAvatar : ImgArray.icAvatar;
    // 未登录状态下默认头像
    const unLoginDefaultAvatar = PlatformUtils.isHarmony() ? ImgArray.harmonyUnloginAvatar : ImgArray.icAvatar;
    const defaultAvatar = this.props.isLogin ? loginDefaultAvatar : unLoginDefaultAvatar;
    return (
      <TouchableOpacity
        activeOpacity={1}
        onPress={() => {
          this.userInfoClick(t('click_head_to_grade_page'));
        }}
        style={_styles.userImg}
      >
        {this.props.isMember && !this.isPc() ? (
          <View style={_styles.cricle}>
            <FastImageView localSource={ImgArray.vAvater} imgStyle={_styles.showRadius} />
            <View style={_styles.showAvatar}>
              {showText ? (
                <Text style={_styles.showText}>
                  {_.truncate(item?.avatar, {
                    length: 2,
                    omission: '',
                  })}
                </Text>
              ) : null}
              {showIcon ? <FastImageView imgUri={avatarIcon} imgStyle={_styles.showIcon} isUser={false} /> : null}
              <Text
                style={[
                  _styles.showText,
                  !this.isApkOrIos() && {
                    marginLeft: showText ? -5 : titleMarginLeft,
                  },
                ]}
              >
                {t('members')}
              </Text>
            </View>
            <View style={{ width: 48, height: 48 }}>
              <FastImageView
                imgUri={this.props.avaImg}
                localSource={this.props?.avaImg ? null : defaultAvatar}
                imgStyle={_styles.avaImg}
                isUser={true}
                onError={() => {
                  this.onLoadResult(false);
                }}
                onLoadSuccess={() => {
                  this.onLoadResult(true);
                }}
              />
            </View>
          </View>
        ) : (
          <FastImageView
            imgUri={this.props.avaImg}
            localSource={this.props.isLogin && this.props.avaImg ? null : unLoginDefaultAvatar}
            imgStyle={_styles.userAva}
            isUser={true}
            onError={() => {
              this.onLoadResult(false);
            }}
            onLoadSuccess={() => {
              this.onLoadResult(true);
            }}
          />
        )}
      </TouchableOpacity>
    );
  };

  onLoadResult = (success: boolean) => {
    const logInfo =  `用户头像加载成功: ${success}。登录状态: ${this.props.isLogin}, 头像地址为空: ${CommonUtils.isEmpty(this.props.avaImg)}` 
    RecordUtils.info(TAG, logInfo);
  }

  // 用户等级内容区域
  userContent = (_styles, mergeStyle, userAccount, isMember, theme, useNewLayout) => {
    const isPc = this.isPc();
    return (
      <View style={[_styles.userInfoWrap]}>
        {this.props.isLogin ? (
          <>
            <TouchableOpacity
              style={_styles.userInfo}
              activeOpacity={1}
              onPress={() => {
                this.userInfoClick(t('click_nickname_to_grade_page'));
              }}
            >
              <Text
                numberOfLines={1}
                style={[
                  _styles.userName,
                  this.getMergeStyle(mergeStyle),
                  {
                    maxWidth: isPc ? '82%' : '100%',
                  },
                ]}
              >
                {this.props.userName}
              </Text>
            </TouchableOpacity>
            {/* 账户名APP展示 */}
            {(useNewLayout || isPc) && userAccount ? this.accountName(_styles, userAccount, mergeStyle) : null}
            {/* 权益模块 */}
            <View style={isPc ? _styles.tagListContainerPc : _styles.tagListContainer}>
              <View style={_styles.tagList}>
                {/* V3会员 如果展示付费会员且已开通则此处不显示*/}
                {this.props.isMember ? null : this.renderMyMember(_styles, theme, useNewLayout)}
                {/* 收货地址 */}
                {!useNewLayout && this.renderAddress(_styles, isMember, mergeStyle, theme)}
              </View>
            </View>
            {/* web端已登录每日签到入口 */}
            {this.state.showTopRightCorner && isPc && this.renderSignIn(_styles)}
          </>
        ) : (
          // 未登录
          this.notLogin(_styles, mergeStyle)
        )}
      </View>
    );
  };

  private renderAddress(_styles: any, isMember: any, mergeStyle: any, theme: any): React.ReactNode {
    return (
      <TouchableOpacity
        activeOpacity={1}
        style={[
          this.isPc() ? _styles.tagTextPc : _styles.tagText,
          this.getBgColorForUseLevel(mergeStyle),
        ]}
        onPress={this.myAddressClick}
      >
        <Text style={_styles.scaleWeb}>
          <Text style={[{ marginRight: 2 }, this.getMergeStyle(mergeStyle)]}>{t('address')}</Text>
          {PlatformUtils.isWap(Dimensions.get('window').width) ? null : (
            <SvgIcon
              viewBox={'-400 0 1024 1024'}
              normalCol={this.getNormalCol(theme, mergeStyle)}
              opacity={0.6}
              iconName={'ic24-more'}
              width={8}
              height={16}
            />
          )}
        </Text>
      </TouchableOpacity>
    );
  }

  private getNormalCol(theme: any, mergeStyle: any): string {
    const color = mergeStyle?.textStyle?.color && !this.props.isMember ? mergeStyle.textStyle.color : theme.C17.color;
    return this.isPc() ? theme.C13.color : color;
  }

  private getMergeStyle(mergeStyle: any) {
    const textStyle = mergeStyle?.textStyle?.color && !this.props.isMember ? mergeStyle.textStyle : null;
    return this.isPc() ? null : textStyle;
  }

  private getNormalColForUseLevel(theme: any, mergeStyle: any): string {
    const color = mergeStyle?.textStyle?.color && !this.props.isMember ? mergeStyle.textStyle.color : theme.C17.color;
    return this.isPc() ? theme.C33.color : color;
  }

  private getBgColorForUseLevel(mergeStyle: any) {
    const bgColor =
      mergeStyle?.textStyle?.color && !this.props.isMember ? { backgroundColor: 'rgba(255,255,255,.2)' } : null;
    return this.isPc() ? null : bgColor;
  }

  renderSignIn = (_styles: any) => {
    return (
      <TouchableOpacity activeOpacity={1} onPress={this.signClick}>
        <FastImageView
          imgUri={`${env.cmsCdnPath}${this.props.headStyle?.topRightCornerIcon}`}
          imgStyle={_styles.signIcon}
          onError={() => this.setState({ showTopRightCorner: false })}
        />
      </TouchableOpacity>
    );
  };

  render() {
    const styleNew = {
      height: 120,
      paddingTop: 36,
      paddingBottom: 36,
      paddingLeft: 32,
      paddingRight: 32,
      alignItems: 'center',
    };
    const { mergeStyle, dataPersonal, isMember, vproList, userAccount, isLogin, isPadH, boxWidth, width } = this.props;
    const item = this.isApkOrIos() ? vproList?.configInfo && JSON.parse(vproList?.configInfo) : vproList;
    const showText = String(item?.showAvatarSetting) === '1' && item.avatar !== '';
    const showIcon = String(item?.showAvatarSetting) === '2' && item.avatarIcon !== '';
    const isDarkTheme = DarkStore.darkBool;
    const avatarIcon = isDarkTheme ? item?.avatarDarkIcon : item?.avatarIcon;
    RecordUtils.info(TAG, 'personal=' + this.props.enableAdvancedFeature);
    const useNewLayout = PlatformUtils.isApp() || PlatformUtils.isWap(width);
    return (
      <WithTheme
        themeStyles={(theme) => styles(theme, this.isPad(), this.isPc(), this.isApp(), isMember, isLogin, isPadH, PlatformUtils.isWap(width))}
      >
        {(_styles, theme) => {
          const padHViewStyle = isPadH ? _styles.padHView : {};
          return (
            <View style={[padHViewStyle, isPadH && { width: boxWidth }]}>
              <View style={[_styles.View, this.isPc() && { flex: 1 }, !isLogin && { alignItems: 'center' }]}>
                {/* 头像 */}
                {this.userHeadImg(_styles, showText, showIcon, item, avatarIcon)}
                {/* 用户名权益 */}
                {this.userContent(_styles, mergeStyle, userAccount, isMember, theme, useNewLayout)}
                {/* 个人资产PC */}
                {this.isPc() && (
                  <View style={[_styles.zcInfo]}>
                    {/* 个人资产 */}
                    <Personal
                      styleNew={styleNew}
                      personaPc={true}
                      imgHeight={48}
                      isLogin={this.props?.isLogin}
                      personalData={dataPersonal}
                      width={this.props.width}
                    />
                  </View>
                )}
                {/* 登录弹窗 */}
                {this.state.showLoginWindow && this.isPc() ? (
                  <LoginWindow targetLink={window.location.href} onClose={() => this.onClose()} />
                ) : null}
              </View>
            </View>
          );
        }}
      </WithTheme>
    );
  }
}
export default componentautoscaling(monitor(dapReportList)(itemExposeHoc(UserInfo)));
